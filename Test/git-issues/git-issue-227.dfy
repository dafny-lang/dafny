// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AppTypes {

datatype Datum = Datum(key:int, value:int)

function EmptyValue() : int
{
    0
}

}

module AbstractMap {
import opened AppTypes

datatype Constants = Constants()
type View = imap<int, int>
datatype Variables = Variables(views:seq<View>)
// A bit of philosophy: Note that, even here in the abstract spec, we maintain
// a list of views that haven't yet been committed to disk. Why? Becuase in the
// future, we may commit some prefix of that view. If we've done 10 alternating
// increments to keys A and B, a filesystem crash could expose *any* of the
// outstanding values -- but no other values, and no views in which B is two
// steps ahead of A. (This is a stronger guarantee than many real filesystems
// give; we may well need to relax it later to allow the implementation more
// freedom.)

predicate completeMap<K(!new),V>(a:imap<K,V>)
{
    forall k :: k in a
}

predicate WF(s:Variables)
{
    && 0 < |s.views|
    && forall i :: 0<=i<|s.views| ==> completeMap(s.views[i])
}

// Dafny black magic: This name is here to give EmptyMap's forall something to
// trigger on. (Eliminates a /!\ Warning.)
predicate InDomain(k:int)
{
    true
}

function EmptyMap() : (zmap : imap<int,int>)
    ensures completeMap(zmap)
{
    imap k | InDomain(k) :: EmptyValue()
}

predicate Init(k:Constants, s:Variables)
    ensures Init(k, s) ==> WF(s)
{
    s == Variables([EmptyMap()])
}

function EphemeralView(k:Constants, s:Variables) : View
    requires WF(s)
{
    s.views[0]
}

predicate Query(k:Constants, s:Variables, s':Variables, datum:Datum)
    requires WF(s)
{
    && datum.value == EphemeralView(k, s)[datum.key]
    && s' == s
}

predicate Write(k:Constants, s:Variables, s':Variables, datum:Datum)
    requires WF(s)
{
    // Prepend a new ephemeral view. Prior view remains on the view
    // stack that's allowed to appear after a crash.
    var newView := EphemeralView(k, s)[datum.key := datum.value];
    s'.views == [newView] + s.views
}

// Report to the user that the disk is synchronized with the memory.
predicate CompleteSync(k:Constants, s:Variables, s':Variables)
    requires WF(s)
{
    && |s.views| == 1
    && s' == s
}

// Some group of writes gets committed, eliminating stale views from before.
predicate PersistWrites(k:Constants, s:Variables, s':Variables, writesRetired:int)
    requires WF(s)
    ensures PersistWrites(k, s, s', writesRetired) ==> WF(s')
{
    && 0 < writesRetired < |s.views|    // leave a view when you're done!
    && s'.views == s.views[..|s.views|-writesRetired]
}

// Forget all non-persisted data.
predicate SpontaneousCrash(k:Constants, s:Variables, s':Variables)
    requires WF(s)
    ensures SpontaneousCrash(k, s, s') ==> WF(s')
{
    s'.views == [s.views[|s.views|-1]]
}

predicate Stutter(k:Constants, s:Variables, s':Variables)
    requires WF(s)
{
    s' == s
}

datatype Step = Query(datum:Datum) | Write(datum:Datum) | CompleteSync | PersistWritesStep(writesRetired:int) | SpontaneousCrashStep | Stutter

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
    requires WF(s)
{
    match step {
        case Query(datum) => Query(k, s, s', datum)
        case Write(datum) => Write(k, s, s', datum)
        case CompleteSync() => CompleteSync(k, s, s')
        case PersistWritesStep(writesRetired) => PersistWrites(k, s, s', writesRetired)
        case SpontaneousCrashStep() => SpontaneousCrash(k, s, s')
        case Stutter() => Stutter(k, s, s')
    }
}

predicate Next(k:Constants, s:Variables, s':Variables)
    requires WF(s)
    ensures Next(k, s, s') ==> WF(s')
{
    exists step :: NextStep(k, s, s', step)
}

}

module Disk {
import opened AppTypes

type LBA = int
datatype Constants = Constants(size:LBA)
datatype Variables = Variables(sectors:seq<Datum>)

predicate ValidLBA(k:Constants, lba:LBA)
{
    0 <= lba < k.size
}

predicate WF(k:Constants, s:Variables)
{
    // All valid lbas are present in the sectors sequence.
    |s.sectors| == k.size
}

predicate Init(k:Constants, s:Variables)
{
    && WF(k, s)
}

predicate Peek(k:Constants, s:Variables, lba:LBA, datum:Datum)
{
    && WF(k, s)
    && ValidLBA(k, lba)
    && s.sectors[lba] == datum
}

function PeekF(k:Constants, s:Variables, lba:LBA) : Datum
    requires WF(k, s)
    requires ValidLBA(k, lba)
{
    s.sectors[lba]
}

predicate Read(k:Constants, s:Variables, s':Variables, lba:LBA, datum:Datum)
{
    && Peek(k, s, lba, datum)
    && s' == s
}

predicate Write(k:Constants, s:Variables, s':Variables, lba:LBA, datum:Datum)
{
    && WF(k, s)
    && ValidLBA(k, lba)
    && s'.sectors == s.sectors[lba := datum]
}

predicate Idle(k:Constants, s:Variables, s':Variables)
{
    && s' == s
}

} // module Disk

module LogImpl {
import opened AppTypes
import Disk
type LBA = Disk.LBA

// The "program counter" for IO steps.
datatype Mode = Reboot | Recover(next:LBA) | Running

datatype Constants = Constants(disk:Disk.Constants)
datatype Variables = Variables(
    // Actual disk state. We get to keep only this state across a crash.
    disk:Disk.Variables,
    // Operating mode, so we can keep track of a recovery read.
    mode:Mode,
    // How much of the disk log is "committed": synced with the value in the log superblock.
    // Drives refinement to abstract 'persistent' state, since this is what we'll see on a recovery.
    diskCommittedSize:LBA,
    // How much of the disk log agrees with the memlog. May exceed diskCommittedSize if we've
    // done PushLogData but not yet PushLogMetadata. We need this pointer to drag the synchrony invariant
    // forward from some PushLogDatas to a PushLogMetadata that updates diskCommittedSize.
    diskPersistedSize:LBA,
    // The memory image of the log. Its prefix agrees with the disk.
    memlog:seq<Datum>)

// The superblock's idea of how big the disk is
function DiskLogSize(k:Disk.Constants, s:Disk.Variables) : int
    requires 1 <= k.size
    requires Disk.WF(k, s)
{
    s.sectors[0].value
}

predicate Init(k:Constants, s:Variables)
{
    // By saying nothing about the other variables, they can "havoc" (take
    // on arbitrary values).
    && Disk.Init(k.disk, s.disk)
    // need a minimum-size disk
    && 1 <= k.disk.size
    // Assume the disk has been mkfs'ed:
    && DiskLogSize(k.disk, s.disk) == 0
    && s.mode.Running?
    && s.diskCommittedSize == 0
    && s.diskPersistedSize == 0
    && s.memlog == []
}

// This organization hides the crash operation in unchecked code, which
// is a little fishy. If I were to add '&&false' in here, the rest of 
// the spec could be totally crash-unsafe, and we'd never know. Perhaps the
// right alternative would be to have the disk belong to a higher-level
// trusted component, the way we do networks in distributed systems.
predicate CrashAndRecover(k:Constants, s:Variables, s':Variables)
{
    && Disk.Idle(k.disk, s.disk, s'.disk)
    && s'.mode.Reboot?
    // By saying nothing about the other variables, they can "havoc" (take
    // on arbitrary values). So clearly we're not relying on memlog.
    && s'.disk == s.disk
}

// Read the superblock, which gives the size of the valid log on disk.
predicate ReadSuperblock(k:Constants, s:Variables, s':Variables)
{
    exists datum ::
        && s.mode.Reboot?
        && Disk.Read(k.disk, s.disk, s'.disk, 0, datum)
        && 0 <= datum.value // If disk holds a negative superblock value, we freeze.
        && s'.mode == Recover(0)
        && s'.diskCommittedSize == datum.value
        && s'.diskPersistedSize == datum.value
        && s'.memlog == []
}

// Pull blocks off the disk until we've read them all.
// Here's a PC-less event-driven thingy. Sorry.
predicate ScanDiskLog(k:Constants, s:Variables, s':Variables)
{
    exists datum ::
        && s.mode.Recover?
        && Disk.Read(k.disk, s.disk, s'.disk, DiskLogAddr(s.mode.next), datum)
        && s.mode.next + 1 < s.diskCommittedSize
        && s'.mode == Recover(s.mode.next + 1)
        && s'.diskCommittedSize == s.diskCommittedSize
        && s'.diskPersistedSize == s.diskPersistedSize
        && s'.memlog == s.memlog + [datum]
}

// We've got all the blocks. Switch to Running mode.
predicate TerminateScan(k:Constants, s:Variables, s':Variables)
{
    && s.mode.Recover?
    && Disk.Idle(k.disk, s.disk, s'.disk)
    && s.mode.next == s.diskCommittedSize   // Nothing more to read
    && s'.mode == Running
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog
}

// In-memory append.
predicate Append(k:Constants, s:Variables, s':Variables, datum:Datum)
{
    && s.mode.Running?
    && s'.disk == s.disk
    && s'.mode == s.mode
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog + [datum]
    && Disk.Idle(k.disk, s.disk, s'.disk)
}

datatype Option<T> = Some(t:T) | None

function {:opaque} FindIndexInLog(log:seq<Datum>, key:int) : (index:Option<int>)
    ensures index.Some? ==>
        && 0<=index.t<|log|
        && log[index.t].key == key
        && (forall j :: index.t < j < |log| ==> log[j].key != key)
    ensures index.None? ==> forall j :: 0 <= j < |log| ==> log[j].key != key
{
    if |log| == 0
        then None
    else if log[|log|-1].key == key
        then Some(|log|-1)
    else
        FindIndexInLog(log[..|log|-1], key)
}

function EvalLog(log:seq<Datum>, key:int) : Datum
{
    var index := FindIndexInLog(log, key);
    if index.Some?
    then log[index.t]
    else Datum(key, EmptyValue())
}

predicate Query(k:Constants, s:Variables, s':Variables, datum:Datum)
{
    && s.mode.Running?
    && datum == EvalLog(s.memlog, datum.key)
    && s'.mode == s.mode
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog
    && Disk.Idle(k.disk, s.disk, s'.disk)
}

// Returns the LBA for an index in the log.
function DiskLogAddr(index:int) : LBA
{
    // +1 to skip superblock.
    index + 1
}

predicate PushLogData(k:Constants, s:Variables, s':Variables)
{
    var idx := s.diskCommittedSize;   // The log index to flush out.
    && s.mode.Running?
    && 0 <= idx < |s.memlog| // there's a non-durable suffix to write
    && Disk.Write(k.disk, s.disk, s'.disk, DiskLogAddr(idx), s.memlog[idx])
    && s'.mode == s.mode
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == idx + 1    // Now idx is durable, too
    && s'.memlog == s.memlog
}

predicate PushLogMetadata(k:Constants, s:Variables, s':Variables, persistentCount:int)
{
    && s.mode.Running?
    // It's okay to bump the metadata forwards even if we don't get it all the
    // way to the end.  Not sure *why* we'd do that, but it will likely be
    // helpful if we later enhance the disk model to be asynchronous (presently
    // the write is atomic).
    && s.diskCommittedSize < persistentCount <= s.diskPersistedSize
    && Disk.Write(k.disk, s.disk, s'.disk, 0, Datum(0, persistentCount))
    && s'.mode == s.mode
    && s'.diskCommittedSize == persistentCount   // drives the refinement to PersistWrites
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog
}

// This promise is br conjunct.
predicate CompleteSync(k:Constants, s:Variables, s':Variables)
{
    && s.mode.Running?
    && s.diskCommittedSize == |s.memlog|
    && s'.mode == s.mode
    && s'.diskCommittedSize == s.diskCommittedSize
    && s'.diskPersistedSize == s.diskPersistedSize
    && s'.memlog == s.memlog
    && Disk.Idle(k.disk, s.disk, s'.disk)
}

datatype Step = 
      CrashAndRecover
    | ReadSuperblock
    | ScanDiskLog
    | TerminateScan
    | Append(datum: Datum)
    | Query(datum: Datum)
    | PushLogData
    | PushLogMetadataStep(persistentCount:int)
    | CompleteSync

predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step)
{
    match step {
        case CrashAndRecover => CrashAndRecover(k, s, s')
        case ReadSuperblock => ReadSuperblock(k, s, s')
        case ScanDiskLog => ScanDiskLog(k, s, s')
        case TerminateScan => TerminateScan(k, s, s')
        case Append(datum) => Append(k, s, s', datum)
        case Query(datum) => Query(k, s, s', datum)
        case PushLogData => PushLogData(k, s, s')
        case PushLogMetadataStep(persistentCount) => PushLogMetadata(k, s, s', persistentCount)
        case CompleteSync => CompleteSync(k, s, s')
    }
}

predicate Next(k:Constants, s:Variables, s':Variables)
{
    exists step:Step :: NextStep(k, s, s', step)
}

predicate DiskLogPlausible(k:Disk.Constants, s:Disk.Variables)
{
    && 1 <= k.size
    && Disk.WF(k, s)
    && 1 <= DiskLogAddr(DiskLogSize(k, s)) <= k.size
}

predicate LogSizeValid(k:Constants, s:Variables)
{
    && 1 <= k.disk.size
    && Disk.WF(k.disk, s.disk)
    && (
        !s.mode.Reboot? ==>
            && s.diskCommittedSize == DiskLogSize(k.disk, s.disk)
            && DiskLogAddr(s.diskCommittedSize) <= DiskLogAddr(s.diskPersistedSize)
            && DiskLogAddr(s.diskPersistedSize) <= k.disk.size
       )
}

predicate LogPrefixAgrees(k:Constants, s:Variables)
{
    s.mode.Running? ==>
        && s.diskPersistedSize <= |s.memlog|
        && LogSizeValid(k, s)
        && (forall i :: 0 <= i < s.diskPersistedSize ==>
            Disk.Peek(k.disk, s.disk, DiskLogAddr(i), s.memlog[i]))
}

predicate ScanInv(k:Constants, s:Variables)
{
    s.mode.Recover? ==>
        && s.mode.next == |s.memlog|
        && s.diskCommittedSize == s.diskPersistedSize
        && s.mode.next <= s.diskCommittedSize
        && (forall i :: 0 <= i < |s.memlog| ==>
            Disk.Peek(k.disk, s.disk, DiskLogAddr(i), s.memlog[i]))
        //XXX && |s.memlog| <= s.diskPersistedSize
}

predicate Inv(k:Constants, s:Variables)
{
    && DiskLogPlausible(k.disk, s.disk)
    && LogSizeValid(k, s)
    && ScanInv(k, s)
    && LogPrefixAgrees(k, s)
}

lemma InvHoldsInit(k:Constants, s:Variables)
    requires Init(k, s)
    ensures Inv(k, s)
{
}

lemma InvHoldsInduction(k:Constants, s:Variables, s':Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
{
}

} // module LogImpl


module RefinementProof {
import opened AppTypes
import opened LogImpl
import AbstractMap

// Interpret a log sequence of Datums as a map
function {:opaque} ILog(log:seq<Datum>) : imap<int, int>
    ensures AbstractMap.completeMap(ILog(log))
{
    imap k | AbstractMap.InDomain(k) :: EvalLog(log, k).value
}

lemma EmptyILog()
    ensures ILog([]) == AbstractMap.EmptyMap()
    // Dafny bug: why can't I just stick this ensures on ILog defn?
{
    reveal_ILog();
}

function DiskLogPrefix(k:Disk.Constants, s:Disk.Variables, len:int) : seq<Datum>
    requires 1 <= DiskLogAddr(len) <= k.size
    requires DiskLogPlausible(k, s)
{
    s.sectors[1..DiskLogAddr(len)]
}

// Interpret the disk as a Datum log
function DiskLog(k:Disk.Constants, s:Disk.Variables) : seq<Datum>
    requires DiskLogPlausible(k, s)
{
    DiskLogPrefix(k, s, DiskLogSize(k, s))
}

// The view reflecting count operations.
function IView(k:Constants, s:Variables, count:int) : AbstractMap.View
    requires Inv(k, s)
    requires 0 <= count <= |s.memlog|
{
    ILog(s.memlog[..count])
}

function INumRunningViews(k:Constants, s:Variables) : int
    requires Inv(k, s)
{
    |s.memlog| - s.diskCommittedSize + 1
}

// Returns a sequence of views of s.memlog, from ..oldest+count-1 working backwards to ..oldest.
// The IRunningViews common case is oldest==diskCommittedSize and count==INumRunningViews,
// so the last entry is ..diskCommittedSize (the persistent view), and the first entry is
// diskCommittedSize+|s.memlog|-diskCommittedSize+1-1 == |s.memlog| -- the whole log, or the
// current ephemeral view.
function {:opaque} IViewsDef(k:Constants, s:Variables, oldest:int, count:int) : (views:seq<AbstractMap.View>)
    requires Inv(k, s)
    requires 0 <= count
    requires 0 <= oldest
    requires oldest + count <= |s.memlog| + 1
    ensures |views| == count
    ensures forall i :: 0<=i<count ==> views[i] == IView(k, s, oldest + count - i - 1)
{
    assert oldest + count - 1 <= |s.memlog|;
    if count==0 then [] else [IView(k, s, oldest + count - 1)] + IViewsDef(k, s, oldest, count-1)
}

function IRunningViews(k:Constants, s:Variables) : (views:seq<AbstractMap.View>)
    requires Inv(k, s)
    requires s.mode.Running?
{
    IViewsDef(k, s, s.diskCommittedSize, INumRunningViews(k, s))
}

// The view when we don't have a memlog
function INotRunningView(k:Constants, s:Variables) : AbstractMap.View
    requires Inv(k, s)
{
    ILog(DiskLog(k.disk, s.disk))
}

function IViews(k:Constants, s:Variables) : seq<AbstractMap.View>
    requires Inv(k, s)
{
    if s.mode.Running?
    then IRunningViews(k, s)
    else [INotRunningView(k, s)]
}

// Refinement to an AbstractMap
function I(k:Constants, s:Variables) : AbstractMap.Variables
    requires Inv(k, s)
{
    AbstractMap.Variables(IViews(k, s))
}

function Ik(k:Constants) : AbstractMap.Constants
{
    AbstractMap.Constants()
}

lemma InvImpliesRefinementInit(k:Constants, s:Variables)
    requires Init(k, s)
    ensures AbstractMap.Init(Ik(k), I(k, s))
{
    EmptyILog();
    assert IViews(k, s) == [AbstractMap.EmptyMap()];  // OBSERVE
} 

lemma InvImpliesWF(k:Constants, s:Variables)
    requires Inv(k, s)
    ensures AbstractMap.WF(I(k, s))
{
    reveal_ILog();
    reveal_FindIndexInLog();
}

lemma LogAppend(log:seq<Datum>, datum:Datum)
    ensures ILog(log + [datum]) == ILog(log)[datum.key := datum.value]
{
    reveal_ILog();
    reveal_FindIndexInLog();
}

lemma PushLogNoop(k:Disk.Constants, s:Disk.Variables, s':Disk.Variables, len:int)
    requires DiskLogPlausible(k, s)
    requires DiskLogPlausible(k, s')
    requires 0 <= len <= DiskLogSize(k, s)
    requires forall i :: 0<=i<len ==> s.sectors[i] == s'.sectors[i] // OBSERVE, probably
    ensures DiskLog(k, s') == DiskLog(k, s)

function {:opaque} UpdateKeySet(log:seq<Datum>) : (keys:set<int>)
    ensures forall i :: 0<=i<|log| ==> log[i].key in keys
    ensures forall k, i :: 0<=i<|log| && !(k in keys) ==> log[i].key != k
{
    if log==[] then {} else UpdateKeySet(log[..|log|-1]) + {log[|log|-1].key}
}

function {:opaque} IndexForKey(log:seq<Datum>, key:int) : (idx:int)
    requires key in UpdateKeySet(log)
    ensures 0<=idx<|log|
    ensures log[idx].key == key
    ensures forall j :: idx < j < |log| ==> log[j].key != key
{
    reveal_UpdateKeySet();
    if log[|log|-1].key == key
    then |log|-1
    else IndexForKey(log[..|log|-1], key)
}

lemma LogIndexFallThrough(log:seq<Datum>, logPrefix:seq<Datum>, logSuffix:seq<Datum>, k:int)
    requires log == logPrefix + logSuffix
    requires forall i :: 0<=i<|logSuffix| ==> logSuffix[i].key != k
    ensures FindIndexInLog(log, k) == FindIndexInLog(logPrefix, k)
    decreases |logSuffix|
{
    reveal_FindIndexInLog();
    if logSuffix != [] {
        var subSuffix := logSuffix[..|logSuffix|-1];
        LogIndexFallThrough(logPrefix + subSuffix, logPrefix, subSuffix, k);
        if |log| > 0 && log[|log|-1].key != k {
            assert log[..|log|-1] == logPrefix + subSuffix;    // OBSERVE (sequences)
        }
    } else {
        assert log == logPrefix;    // OBSERVE (sequences)
    }
}

// If you don't find k in the suffix of a log, you can read the prefix.
lemma LogFallThrough(log:seq<Datum>, logPrefix:seq<Datum>, logSuffix:seq<Datum>, k:int)
    requires log == logPrefix + logSuffix
    requires forall i :: 0<=i<|logSuffix| ==> logSuffix[i].key != k
    ensures ILog(log)[k] == ILog(logPrefix)[k]
{
    reveal_ILog();
    reveal_FindIndexInLog();
    LogIndexFallThrough(log, logPrefix, logSuffix, k);
}

lemma PushLogMetadataRefinement(k:Constants, s:Variables, s':Variables, persistentCount:int)
    requires LogImpl.PushLogMetadata(k, s, s', persistentCount)
    requires Inv(k, s)
    ensures AbstractMap.WF(I(k, s))
    ensures AbstractMap.WF(I(k, s'))
    ensures AbstractMap.Next(Ik(k), I(k, s), I(k, s'))
{
    var Ik := Ik(k);
    var Is := I(k, s);
    var Is' := I(k, s');
    var writesRetired := persistentCount - s.diskCommittedSize;
    assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.PersistWritesStep(writesRetired)); // OBSERVE witness (Step)
}

lemma InvImpliesRefinementNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires Inv(k, s)
    ensures AbstractMap.WF(I(k, s))
    ensures AbstractMap.WF(I(k, s'))
    ensures AbstractMap.Next(Ik(k), I(k, s), I(k, s'))
{
    var Ik := Ik(k);
    var Is := I(k, s);
    var Is' := I(k, s');

    InvImpliesWF(k, s);
    InvHoldsInduction(k, s, s');  // OMG line unecessary: of course Dafny is just doing this whole proof again...
    InvImpliesWF(k, s');

    var step :| NextStep(k, s, s', step);

    match step {
        case CrashAndRecover => {
            if (s.mode.Running?) {
                assert DiskLog(k.disk, s.disk) == s.memlog[..s.diskCommittedSize];  // OBSERVE
            }
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.SpontaneousCrashStep());
        }
        case ReadSuperblock => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case ScanDiskLog => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case TerminateScan => {
            assert DiskLogPrefix(k.disk, s.disk, |s.memlog|) == s.memlog;   // OBSERVE
            calc {
                Is';
                IViews(k, s); // uncomment this line to witness bizarreness
                Is;
            }
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case Append(datum) => {
            LogAppend(s.memlog, datum);
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Write(datum));
        }
        case Query(datum) => {
            reveal_ILog();
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Query(datum));
        }
        case PushLogData => {
            PushLogNoop(k.disk, s.disk, s'.disk, DiskLogSize(k.disk, s.disk));
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
        case PushLogMetadataStep(count) => {
            PushLogMetadataRefinement(k, s, s', count);
        }
        case CompleteSync => {
            assert AbstractMap.NextStep(Ik, Is, Is', AbstractMap.Stutter());
        }
    }
} 


} // module RefinementProof
