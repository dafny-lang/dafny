/* Repro test case for https://github.com/dafny-lang/dafny/issues/3048
 * author: Nathan Taylor <ntaylor@cs.utexas.edu>
 *
 * This file should not pass the resolver and provide a counterexample,
 * but should not crash the language server either.
 */

/* Types */

newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i <= UINT64_MAX
const UINT64_MAX := 0x1_0000_0000_0000_0000 - 1

newtype{:nativeType "ulong"} uint8 = i:int | 0 <= i <= UINT8_MAX
const UINT8_MAX := 0x100 - 1

type Block = seq<uint8>
type Zone = seq<Block>

/* a zone map is a sequence of contiguous half-open intervals. */

predicate zone_map_well_formed(n_blocks: uint64, zone_map: seq<(uint64, uint64)>) {
  && 0 < |zone_map| as int
  && zone_map[0].0 == 0
  && zone_map[|zone_map| - 1].1 == n_blocks
  && zone_map_ordered_total(zone_map)
}

predicate zone_map_ordered_total(zone_map: seq<(uint64, uint64)>) {
  && 0 < |zone_map| as int
  && (forall i :: 0 <  i < |zone_map| ==> zone_map[i-1].1 == zone_map[i].0)
  && (forall i :: 0 <= i < |zone_map| ==> zone_map[i].0 < zone_map[i].1)
  && (forall i :: 0 <= i < |zone_map| ==> (zone_map[i].1 - zone_map[i].0) as int < UINT64_MAX)
}

/* State transitions take Constants as, well, constant. */

datatype Constants = Constants(
  n_blocks: uint64,
  zone_map: seq<(uint64, uint64)> // [b, e)
)

/* Meanwhile, States change as we transition, well, states. */

datatype State = State(
  /* A zone is a contiguous region of a disk. */
  zones: seq<Zone>,

  /* Which buffer will we fault the next write's zone over into? */
  buffer_zone: int,

  /* Logical zone -> physical zone remapping (to account for the
   * buffer zone, which will float around as writes happen) */
  buffer_map: seq<int>
)

predicate Valid(c: Constants, s: State) {
  && zone_map_well_formed(c.n_blocks, c.zone_map)
  && |s.zones| == |c.zone_map|
  && (forall z :: 0 <= z < |s.zones| ==>
      |s.zones[z]| == (c.zone_map[z].1 - c.zone_map[z].0) as int)
}


predicate Write(c: Constants, s: State, s': State, lba: uint64, val: Block)
  requires Valid(c, s)
  requires 0 <= lba < c.n_blocks
{
  var (lzone, off) := (0,0);
  var pzone := s.buffer_map[lzone];

  var src_zone := s.zones[pzone];
  var dst_zone := src_zone[ off := val ];

  && |s.zones| == |s'.zones|

  // The zone containing the block we want to destructively write
  // is now the new buffer zone

  // Our former buffer zone now contains the zone with the
  // destructive update
  && s'.zones[s.buffer_zone] == dst_zone

  // No other zones are touched
  && (forall i :: 0 <= i < |s'.zones| ==>
      (i != pzone && i != s.buffer_zone ==> s.zones[i] == s'.zones[i]))
}

lemma WritePreservesValid(c: Constants, s: State, s': State, lba: uint64, val: Block)
  requires Valid(c, s)
  requires Write(c, s, s', lba, val);
  ensures Valid(c, s')
{}
