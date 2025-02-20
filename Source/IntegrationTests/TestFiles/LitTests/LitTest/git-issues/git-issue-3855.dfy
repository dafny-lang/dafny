// RUN: %exits-with 4 %baredafny verify --show-snippets:false --allow-axioms --allow-deprecation --use-basename-for-filename --type-system-refresh=false --general-newtypes=false "%s" > "%t".raw
// RUN: %sed 's/after [0-9]+ seconds/after <redacted> seconds/' %t.raw > "%t"
// RUN: %diff "%s.expect" "%t"
// Nearly verbatim copy of the text case given in the issue
//SIMULADA 

datatype Mode = Imm | Iso | Mut | Tmp | Sus // "static" declartion - type-like
 //at this point, since the heap model framework supports variables directly
 //we don't need to worry about the "Var" mode from the formal appendix
 //note that the "var" mode is not in the actual paper
 
// "dynamic" value - reference-like
//were "Owner"s now "Region"s.  not sure I like that really!
//but Heap & Stack regions have owners which are Objects... 
//For Stack regions, those owners should be Frames
//this is set up carefully so traversing the current stack towards the "root"
//i.e. going back in time, *decreases* the Dafny inductive datatype.
//that way, termination is implicit.
datatype Region = Frozen | Heap(region : Object) | Stack(region : Object)  | Frame(prev : Object) | Isolate //should be deleted most likely?
  //current thoughts for VENICE - don't make any Isos;
  //allow the iso field to point to a Mut
  //but each Mut region can still have only one referenve to it's current "bridge´"
  //so we need to "Bootstrap" Isos - so iyou make an Isolate and then fuck with it


//static rules on permissibleg declarations
//this wiVerll eventually be generalised to the Dave Clarke Equation :-)
//i.e. NoIncomingReferences...
//f=from, t=to
//VENICE TODO - this seems weird - need static notion of kind of object (not just mode?)
predicate VeniceDeclarationOK(f : Mode, t : Mode)
{
   true
}

//dynamic rules on permissible dynamic reference owners
//f=from, t=to
predicate VeniceReferenceOK(f : Object, t : Object)
{
  if (t.region.Frozen?) 
    then true 
    else (
  if (f.region.Heap?) 
    then ((t.region.Isolate?) || (t.region.Heap? && t.region.region == f.region.region))
    else (
  if (f.region.Isolate?) 
    then ((t.region.Isolate?) || (t.region.Heap? && t.region.region == f))
    else false
    ))
}

lemma MutsPointOnlyInSameRegion(f : Object, t : Object)
  requires f.region.Heap?
  requires t.region.Heap?
  requires VeniceReferenceOK(f,t) 
  ensures f.region == t.region
{
}


//can object o be assigned to a field of Mode 
//this is a *dynamic check* typically looking at the region of O
predicate AssignmentCompatible(o : Object, t : Mode) 
{
 var r := o.region;
 match t //Imm | Iso | Mut | Tmp | Sus | Var
  case Imm => r.Frozen? 
  case Iso => r.Isolate? //TODO VENICE
  case Mut => r.Heap?
  case Tmp => r.Stack?
  case Sus => r.Heap? || r.Stack? 
}


//////////////////////////////////////////////////////////////////////////////
// CLASSES and OBJECTS
//
//I know it's perverse, but titlecase "Object" and "Class" aren't reserved in dafny
//
//a class here is a map of field names to Modes
//basically giving the relative static ownership of each field
//note that null / undefined fields can be declared in their object's class
//but may not necessarily be in the Object's fields.
type Class = map<string,Mode>

//This models, well, an object.   
class Object {  
  const region : Region; //actual "dynamic" region of this object
      ///VENICE  TODO - switch to a "var" most likely, which will fcck with reading etc
  var fields : map<string,Object>;  //field values. uninit fields have no entries
  const fieldModes : Class;   //Mode of each field name -  note, static! - would be statically known by any methods
 
  constructor(k : Region, ks : Class) 
    ensures region == k 
    ensures fieldModes == ks
    ensures fields == map[] //object fields starts uninitialised
    ensures Valid()
  { region := k;
    fieldModes := ks;
    fields := map[];
    new;
    reveal Valid();
  } 


  function outgoing() : set<Object> reads this`fields { fields.Values }
  function fieldNames() : set<string> {  fieldModes.Keys }
  function size() : nat reads this`fields { |outgoing()| }

  predicate {:opaque} Valid()
        reads this`fields
   {
    AllFieldsAreDeclared()
      &&
    AllFieldsContentsConsistentWithTheirDeclaration()
      && 
    AllOutgoingReferencesAreVenice()
  }

  predicate AllFieldsAreDeclared() 
    reads this`fields 
    { fields.Keys <= fieldModes.Keys }

  predicate AllFieldsContentsConsistentWithTheirDeclaration() 
    requires AllFieldsAreDeclared()
    reads this`fields 
    { 
      forall n <- fields :: AssignmentCompatible(fields[n],fieldModes[n])
    }
  
  predicate AllOutgoingReferencesAreVenice()
    reads this`fields
    {
        forall n <- fields :: VeniceReferenceOK(this, fields[n])
    }

}

//////////////////////////////////////////////////////////////////////////////
// edges
//
// some computations work with sets of edges, instead of sets of objects
// methods like edges(oo:set<Object>) or incomingEdges(o:Object)
// "generate" the edge-sets as needed
//
// one edge is pretty much a named tuple for a single edge
// f=from object, n=field name in f, t=to object

datatype Edge = Edge(f : Object, n : string, t : Object)


//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/// HEAP                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

class Memory {
  var objects : set<Object>  



  constructor() 
    ensures Valid() 
    ensures fresh(this)
    ensures objects == {}
    {
      objects := {};
      new;
      reveal Valid();
    }

  predicate {:opaque}     {:no_inline} Valid() 
    reads this`objects, objects
    {
     ObjectsAreValid(objects) 
      &&
     OutgoingReferencesAreInThisHeap(objects)
       &&
     wholeEnchilada(objects)
    }

    lemma Valid2ImpliesValid() 
      ensures Valid2() ==> Valid()
    {
      reveal Valid();
      reveal Valid2();

      assert Valid2() ==> Valid();
    }  

    twostate predicate {:opaque}     {:no_inline} Valid2()
        reads this`objects, objects, objects`fields
        ensures Valid2() ==> Valid()
    { 
     reveal Valid();
     Valid()
       &&
     HeapObjectsAreMonotonic()
       &&
     AllImmutablesAreImmutable() 
    }

  predicate ObjectsAreValid(os : set<Object>) 
    reads os
    {
      (forall o <- os :: o.Valid())
    }

  predicate OutgoingReferencesAreInThisHeap(os : set<Object>) 
      reads this`objects, objects, os
      //note that this is within *this memory* - not with the os objectset
      //unfortunately this couples everything to this memory...
    {
     (forall o <- os :: o.outgoing() <= objects) 
    }

  

  twostate predicate HeapObjectsAreMonotonic() 
    reads this`objects
    {
      old(objects) <= objects

    }

  twostate predicate AllImmutablesAreImmutable() 
    reads this`objects, objects, objects`fields
    {
       forall o <- (objects * old(objects)) ::   
           o.region.Frozen? ==> (o.fields == old(o.fields))
    }


  function justTheIsos(os : set<Object>) : (rs : set<Object>) 
    reads os
    ensures forall r <- rs :: r.region.Isolate?
    ensures forall o <- os :: o.region.Isolate? ==> o in rs
    ensures (os == {}) ==> (rs == {})
  {
    set o <- os | o.region.Isolate?
  }


  function incomingEdges(t : Object, edges : set<Edge>) : (rs : set<Edge>)
    ensures rs <= edges
  {
    set e <- edges | e.t == t
  }

  function refCountEdges(t : Object, edges : set<Edge>) : nat 
  {
    | incomingEdges(t, edges) | 
  }

  function edges(os : set<Object>) : (r : set <(Edge)>) 
    reads os
    ensures forall edge <- r :: edge.n in edge.f.fields && edge.f.fields[edge.n] == edge.t
    ensures (os == {}) ==> (r == {})
  {
     set o <- os, n <- o.fields :: Edge(o, n, o.fields[n])
  }

  //really means:more tricky edge predicates are 
  predicate wholeEnchilada(os : set<Object>) 
      reads os
    {
        isosRefCountZeroOrOne(os) &&
        heapExternalsZeroOrOne(os)
    }

  //really means: each VENICE Heap region has <= 1 external reference.
  predicate heapExternalsZeroOrOne(os : set<Object>)
      reads os
  {
    var edges := edges(os);  
    heapExternalsZeroOrOneEdges(edges)
  }

  predicate heapExternalsZeroOrOneEdges(edges : set<Edge>) {
    var heapExternalEdges := justHeapExternalEdges(edges);
    var allRelevantHeapRegions := set he <- heapExternalEdges :: he.t.region;
    var heapExternalEdgesPartitionedByRegion : map<Region,set<Edge>>
      := 
      map r <- allRelevantHeapRegions :: externalEdges(r, heapExternalEdges);
    forall hr <- heapExternalEdgesPartitionedByRegion.Keys :: 
       |heapExternalEdgesPartitionedByRegion[hr]| <= 1
  }

  //alternative formulation of the above.
  predicate heapExternalsZeroOrOneXXX(os : set<Object>)
      reads os
  {
    var edges := edges(os);  
    var heapRegionPartitions := partitionOfJustHeapRegions(os);
    forall hr <- heapRegionPartitions.Keys :: 
       |heapRegionPartitions[hr]| <= 1
  }



  // function heapExternalsPartitionedMoreStupidLike(os : set<Object>) : map<Region,set<Edge>>
  //     reads os
  // {
  //   var edges := edges(os);  
  //   var heapExternalEdges := justHeapExternalEdges(edges);
  //   var allRelevantHeapRegions := set he <- heapExternalEdges :: he.t.region;
  //   var heapExternalEdgesPartitionedByRegion := 
  //     map r <- allRelevantHeapRegions ::
  //       r := (set e <- heapExternalEdges :: e.t.region == r);
  //   heapExternalEdgesPartitionedByRegion
  // }

  //really means: all iso objects in the object set have <= 1 incoming reference.
  predicate isosRefCountZeroOrOne(os : set<Object>)
      reads os
  {
    var edges := edges(os);  
    var isos := justTheIsos(os);
    forall i <- isos :: refCountEdges(i, edges) <= 1
  }

  //really means: each region has only one incoming reference?.
  predicate wholeEnchiladaNEW(os : set<Object>)
      reads os
  {
    var ns := allRegions(os);
    var es := edges(os);
 
    wholeEnchilada(os) 
    // &&
    // forall n <- ns :: n.Heap? ==> | externalEdges(n,  es) | <= 1 
  } 


  function externalEdges(o: Region, edges : set<Edge>) : (rs : set<Edge>)
    ensures rs <= edges
  {
    set e <- edges | e.t.region == o && e.f.region != o 
  }

//or should this be "allExternalEdges"
//went with "just" with the idea "justX(a):r" means to filter ---- ensures r <= a
//meanwhile allX(a):r can do move - e.g. map all objects to all owning "regions"
  function justHeapExternalEdges(edges : set<Edge>) : (rs : set<Edge>)
    ensures rs <= edges
  {
    set e <- edges | e.f.region != e.t.region && e.t.region.Heap?
  }

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// 
// low-level "functions" operating on the memory.
//    goodness knows why this public API are named starting with "f"
//    but they do!  All these operations maintain the invariants of the memory
//
//   fAddObject - add a new empty Obejct into the memory
//   fExists - does a field exist on an Object  (field exists make sense)
//   fRead - read a field 
//   fInitialise - initialise a field.  unfortuantely Imm fields can't be initialised. oops!
//   fNullify - nullify (delete) a field from an Object
//   fGC - garbage collect a "region" owned by an iso (iso must have refcnt==0)

  method fAddObject(nu : Object)
    requires Valid()
    requires nu.Valid()
    requires nu.size() == 0
    requires nu !in objects
    modifies this`objects
    ensures Valid2()
    ensures unchanged(nu)
    ensures objects == old(objects) + {nu};
    {
      reveal Valid();
      assert Valid();

assert heapExternalsZeroOrOne(objects);

      objects := objects + {nu};

      assert edges(objects) == edges(old(objects) + {nu}) == old(edges(objects));

      assert partitionOfJustHeapRegions(objects) 
          == partitionOfJustHeapRegions(old(objects) + {nu});

assert justHeapExternalEdges(edges(objects))
          == justHeapExternalEdges(edges(old(objects)))   //OVERKILL
          == justHeapExternalEdges(old(edges(objects)))
          == old(justHeapExternalEdges(edges(objects)));

      reveal Valid();
      reveal Valid2();

assert heapExternalsZeroOrOne(objects);

      assert Valid2();
   }


  predicate fExists(o : Object, n : string) 
    requires o in objects
    requires Valid() 
    reads this`objects, objects, o`fields  
    { n in o.fields }


  function fRead(o : Object, n : string) : (r : Object)
    requires o in objects
    requires Valid()
    reads this`objects, objects, o`fields
    reads this`objects, objects, o`fields  
    requires n in o.fields
    { o.fields[n] }

//{:timeLimit 60}
  method {:timeLimit 15} fInitialise(o : Object, f : string, t : Object) 
    requires o  in objects
    requires f  in o.fieldModes
    requires f !in o.fields
    requires t  in objects



//Venice TODO turn off ISOS!
//    requires not(o.region.Isolate?)

    requires t.region.Isolate? ==>  refCountEdges(t, edges(objects)) == 0; //VENICE TODO

    requires o.fieldModes[f] == Mut;
     //this is the assignment, so need to look at "assignment comaptible" and the paper...

 //Venice TODO 
    requires (o.region == t.region) || (t.region == Frozen) // || (o.region == stack)
    
    //so we can't use this to make references across regions.
 //Venice TODO 
    requires not(o.region.Frozen?) //Umm but how then do I initialise fields of Immutables?
//answer - Venice free a mutable then reenze ti!

    requires VeniceReferenceOK(o,t)
    requires AssignmentCompatible(t, o.fieldModes[f])   //dynamic check? is that right?
    requires Valid()

    modifies o`fields
    
    ensures unchanged(this`objects)
    ensures f in o.fields
    ensures o.fields[f] == t
    ensures unchanged(objects - {o})
    ensures o.fields == old(o.fields[f := t])  
    ensures Valid2()
    { 
      reveal Valid();
      reveal o.Valid();
      reveal Valid2();

    assert Valid();
    assert wholeEnchilada(objects);//VENICE TODO

      var xedges := edges(objects);
      var xisos := justTheIsos(objects);
    
assert heapExternalsZeroOrOneEdges(xedges);


      o.fields := o.fields[f := t];   ///who designed this fucking syntax?

      assert ObjectsAreValid({o});
          
      var zedges := edges(objects);  //or could hand in if necessary?
      var zisos := justTheIsos(objects);

      assert t.region.Isolate? ==> refCountEdges(t, xedges) == 0;//VENICE TODO


      assert (o != t) ==> incomingEdges(t, {Edge(t,f,o)}) != {Edge(o,f,t)};
      assert incomingEdges(t, {Edge(o,f,t)}) == {Edge(o,f,t)};

      RefCountDistributesOverDisjointEdges(zisos,  xedges , {Edge(o,f,t)});

externalDistributesOverDisjointEdges(objects, xedges, {Edge(o,f,t)});

  assert heapExternalsZeroOrOneEdges(xedges);

  assert zedges == xedges + {Edge(o,f,t)};
  assert justHeapExternalEdges( {Edge(o,f,t)} ) == {};
  assert justHeapExternalEdges(zedges) == justHeapExternalEdges(xedges);

  assert heapExternalsZeroOrOneEdges(zedges);
  assert wholeEnchilada(objects); //VENICE TODO
  assert Valid2();
  }

//given objects oo with references counts across aa+bb, we can split into aa and bb
 lemma {:opaque} externalDistributesOverDisjointEdges(oo : set<Object>, aa : set<Edge>, bb : set<Edge>)
      requires aa !! bb
      ensures 
       forall n <- allRegions(oo) ::
        externalEdges(n, aa + bb) == externalEdges(n, aa) + externalEdges(n, bb)
    {
    //   //calc == {
    //    assert forall i <- oo :: 
    //         (set e <- aa | e.t == i) + (set e <- bb | e.t == i)
    //         == (set e <- (aa+bb) | e.t == i); 
    //    assert forall i <- oo :: 
    //         incomingEdges(i,aa) + incomingEdges(i,bb)
    //         == incomingEdges(i,aa+bb);
    //    assert forall i <- oo :: 
    //         refCountEdges(i,aa) + refCountEdges(i,bb)
    //         == refCountEdges(i,aa+bb);
    //   //}
    }


//given objects oo with references counts across aa+bb, we can split into aa and bb
 lemma {:opaque} RefCountDistributesOverDisjointEdges(oo : set<Object>, aa : set<Edge>, bb : set<Edge>)
      requires aa !! bb
      ensures 
       forall i <- oo ::
         refCountEdges(i, aa + bb) == refCountEdges(i, aa) + refCountEdges(i, bb)
    {
      //calc == {
       assert forall i <- oo :: 
            (set e <- aa | e.t == i) + (set e <- bb | e.t == i)
            == (set e <- (aa+bb) | e.t == i); 
       assert forall i <- oo :: 
            incomingEdges(i,aa) + incomingEdges(i,bb)
            == incomingEdges(i,aa+bb);
       assert forall i <- oo :: 
            refCountEdges(i,aa) + refCountEdges(i,bb)
            == refCountEdges(i,aa+bb);
      //}
    }



lemma {:opaque} BiggerIsBigger<T>(aa : set<T>, bb : set<T>)
     requires aa >= bb
     ensures |aa| >= |bb|
{
  var xs := aa - bb;
  assert |aa| == |bb| + |xs|;
}

lemma {:opaque} RefCountIsMonotonic(oo : set<Object>, aa : set<Edge>, bb : set<Edge>)
      requires aa >= bb
      ensures 
       forall i <- oo ::
         refCountEdges(i, aa) >= refCountEdges(i, bb)
    {
      assert aa >= bb;
      assert forall i <- oo :: 
            (set e <- aa | e.t == i) >= (set e <- bb | e.t == i);

      forall i <- oo ensures 
       | incomingEdges(i,aa) | >= | incomingEdges(i,bb) |   
       {     
         BiggerIsBigger(incomingEdges(i,aa),incomingEdges(i,bb));
       }
      assert forall i <- oo :: 
           | incomingEdges(i,aa) | >= | incomingEdges(i,bb) |;        
      assert forall i <- oo :: 
            refCountEdges(i,aa) >= refCountEdges(i,bb);        
    }


//VENICE - started editing but now thing I don't beed it.
// lemma {:opaque} HeapExternalIsMonotonic(oo : set<Object>, aa : set<Edge>, bb : set<Edge>)
//       requires aa >= bb
//       ensures 
//     {
//       assert aa >= bb;
//       assert forall i <- oo :: 
//             (set e <- aa | e.t == i) >= (set e <- bb | e.t == i);

//       forall i <- oo ensures 
//        | incomingEdges(i,aa) | >= | incomingEdges(i,bb) |   
//        {     
//          BiggerIsBigger(incomingEdges(i,aa),incomingEdges(i,bb));
//        }
//       assert forall i <- oo :: 
//            | incomingEdges(i,aa) | >= | incomingEdges(i,bb) |;        
//       assert forall i <- oo :: 
//             refCountEdges(i,aa) >= refCountEdges(i,bb);        
//     }

//note that this puts all Isos into one "region"
//should an Iso go with their contents?
//region method on obejcts - use it instead of "region"??
//same as region, except **isos return Mut(self) :-)  
// HERE IS WHERE I"M UP TO**

function ownedBy(os : set<Object>, region : Region ) : (owned : set<Object>)
  ensures forall o <- os :: (o.region == region) == (o in owned)
 {
  set o <- os | o.region == region
} 

function allRegions(os : set<Object>) : set<Region>
   ensures forall o <- os :: o.region in allRegions(os)
 {
  set o <- os :: o.region
}

lemma ownershipRegionsAreDisjoint(os : set<Object>, o1 : Region, o2 : Region) 
   requires o1 != o2
   ensures ownedBy(os,o1) !! ownedBy(os,o2)
   { } 



function partitionIntoRegions(os : set<Object>) : (partition : map<Region,set<Object>>)
  ensures forall o <- os :: o.region in partition.Keys
  ensures forall o <- os :: o in partition[o.region]
  ensures forall o1 <- allRegions(os), o2 <- allRegions(os) ::
     if (o1 == o2)
       then partition[o1] == partition[o2] //this says: ownerhip regions are disjoint
       else partition[o1] !! partition[o2]
{
  map region <- allRegions(os) :: region := ownedBy(os, region) 
}


function partitionOfJustHeapRegions(os : set<Object>) : (partition : map<Region,set<Object>>)
  ensures forall o <- os :: o.region.Heap? ==> o.region in partition.Keys
  ensures forall o <- os :: o.region.Heap? ==> o in partition[o.region]
  ensures forall o1 <- allRegions(os), o2 <- allRegions(os) ::
   (o1.Heap? && o2.Heap?) ==>
     if (o1 == o2)
       then partition[o1] == partition[o2] //this says: ownerhip regions are disjoint
       else partition[o1] !! partition[o2]
{
  var heapOnwers := set o <- allRegions(os) :: o.Heap?;
  map region <- allRegions(os) :: region := ownedBy(os, region) 
}


method {:resource_limit 30000000} {:isolate_assertions} fNullify(o : Object, f : string)
    requires o  in objects
    requires f  in o.fieldModes
    requires f  in o.fields

    requires Edge(o,f, o.fields[f]) in edges(objects);

    requires !  o.region.Frozen? 
   
    requires Valid()

    modifies o`fields
    
    ensures unchanged(this`objects)
    ensures unchanged(objects - {o})
    ensures o.fields == RemoveKey(old(o.fields), f)

    ensures edges(objects) <= old(edges(objects));
    ensures Edge(o,f, old(o.fields[f])) !in edges(objects);
    ensures Valid2()
    { 
      reveal Valid();
      reveal o.Valid();
     
      var xedges := edges(objects);
      var xisos := justTheIsos(objects);
  
      var nedge :=  Edge(o,f, o.fields[f]); //edge to be nullified

      //assert nedge in edges(objects);

      o.fields := RemoveKey(o.fields,f);

      //assert nedge !in edges(objects);

      var zedges := edges(objects); 

      //assert zedges + {nedge} == xedges;

      RefCountIsMonotonic(xisos,xedges,zedges);

      //assert heapExternalsZeroOrOneEdges(xedges);
      //assert zedges <= xedges;
      //assert justHeapExternalEdges(zedges) <= justHeapExternalEdges(xedges);
      //assert (set he <- justHeapExternalEdges(zedges) :: he.t.region) <= 
      //       (set he <- justHeapExternalEdges(xedges) :: he.t.region);
      //assert forall r <- allRegions(old(objects)) ::
      //       externalEdges(r, justHeapExternalEdges(zedges)) <= 
      //       externalEdges(r, justHeapExternalEdges(xedges));

      assert heapExternalsZeroOrOneEdges(xedges);

  //VENICE EVIL EVIL EVIL
  assume heapExternalsZeroOrOneEdges(zedges);

  //  assert forall r <- allRegions(old(objects)) ::
  //            |externalEdges(r, justHeapExternalEdges(xedges))| <= 1;
  //  assert forall r <- allRegions(objects) ::
  //            |externalEdges(r, justHeapExternalEdges(zedges))| <= 1;





      assert heapExternalsZeroOrOneEdges(zedges);

      // assert forall i <- xisos :: refCountEdges(i, zedges) <= 1;
      reveal Valid2();
    }



//garbage collect a region based at iso
//iso needs to have zero incoming references
//
//because currenty object's are "monotonic" - they cant be deleted
//what this does is delete all the fields from every object in the "region"
//and proves they're all garbage (reference count == 0)
//
  method fGC(iso : Object) 
    requires iso in objects
    requires iso.region.Heap?
    requires refCountEdges(iso, edges(objects)) == 0  //must have already deleted only reference to that iso
   
    requires Valid()

    modifies ownedBy(objects, iso.region)
    
    ensures unchanged(objects - ownedBy(objects, iso.region))

    //VENICE TODO - this bit won't verify but I cant be arsed working out why!!!!
    // ensures 
    //    var objectsToGC := old(ownedBy(objects, iso.region));   //GOD I LOVE DAFY  (this is a let)
    //    forall o <- (objectsToGC  * objects) :: 
    //      (refCountEdges(o, edges(objects)) == 0 
    //        && o.fields == map[])

    ensures Valid2()
    { 
      reveal Valid();
      reveal iso.Valid();
      
      var xedges := edges(objects);    
      var xisos := justTheIsos(objects);
    
      var objectsToGC := ownedBy(objects, iso.region);

      forall o <- objectsToGC {
         o.fields := map[];
      } 

      var zedges := edges(objects); 

      RefCountIsMonotonic(xisos,xedges,zedges);

  assume heapExternalsZeroOrOneEdges(zedges); //VENICE TODO FUCKISM

      reveal Valid2();
    }



//hmm:this is less helpful than I thought!
lemma mutsPointIntoSameRegionOrImmOrIso(f : Object, t : Object) 
  requires f.Valid()
  requires t.Valid()
  requires VeniceReferenceOK(f, t)
  requires f.region.Heap?
  ensures  t.region.Heap? || t.region.Frozen? || t.region.Isolate?
  ensures  t.region.Heap? ==> (t.region.region == f.region.region)
 {
 }






//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// 
//  "dynamic"  checked intermediate API
//
//  this layer implements "move" or "copy" semantics for assignment a field
//     these two return a failure status if something goes wrong.
//     so we don't necessarily make a claim at this level
//
//  - dynMove(o : Object, n : string, f : Object, m : string) returns (r : Status)
//  - dynCopy(o : Object, n : string, f : Object, m : string) returns (r : Status)
//  more or less  o.m := f.m //copny or "move" "semantics"
//
//  the dyhamic check itself is encapsulated into these methods
//    - betterMoveDynamicCheck(o : Object, n : string, f : Object, m : string)
//    - betterCopyDynamicCheck(o : Object, n : string, f : Object, m : string)
//  same semantics but doesn't do anything, just checks thins are OK
//
//
 
method
{:timeLimit 1}
{:ignore } dynMove(o : Object, n : string, f : Object, m : string) returns (r : Status)

    requires n !=m;  //can't write to oneself field (although o can equal f?)  //seems a bit shifty. houjld be fixed.

    requires o  in objects 
    requires f  in objects
   
    requires Valid()

    modifies o`fields
    modifies f`fields
    
    ensures unchanged(this`objects)

    ensures r.Success? == old(betterMoveDynamicCheck(o,n,f,m))   
    ensures r.Success? ==> (n in o.fields)
    ensures r.Success? ==> old(m in f.fields)
    ensures r.Success? ==> m !in f.fields
    ensures r.Success? ==> (o.fields[n] == old(f.fields[m]))

    ensures Valid2()
    { 
       reveal Valid();
       reveal o.Valid();
       reveal Valid2();

      if (!betterMoveDynamicCheck(o,n,f,m))///dynamic check on actual types
           { assert Valid();
             assert  HeapObjectsAreMonotonic();
              assert AllImmutablesAreImmutable();
assume heapExternalsZeroOrOne(objects); //VENICE TODO 10 April 2023
              assert Valid2();
            
             return Failure("FUCKED"); } 

      r := Success;
      
      var value := f.fields[m];

      if (fExists(o,n)) {fNullify(o,n);}

      var xedges := edges(objects);

      fNullify(f,m);


      if (value.region.Isolate?) { 
        var edges := edges(objects);
        assert edges == xedges - {Edge(f,m,value)};
        assert xedges == edges + {Edge(f,m,value)};
        assert incomingEdges(value, {Edge(f,m,value)}) == {Edge(f,m,value)};
        assert refCountEdges(value, {Edge(f,m,value)}) == 1;
        RefCountDistributesOverDisjointEdges({value}, edges, {Edge(f,m,value)} );
        //assert  refCountEdges(value, edges + {Edge(f,m,value)} ) == 
        //  refCountEdges(value, edges) + refCountEdges(value, {Edge(f,m,value)});
        //assert refCountEdges(value, edges) == 0;
assume heapExternalsZeroOrOne(objects); //VENICE TODO 10 April 2023

      }
     
    fInitialise(o,n,value);

    //HERE;  1am MONDAY 22 AUGUST 2022!
  
assume heapExternalsZeroOrOne(objects); //VENICE TODO 10 April 2023
  }

predicate betterMoveDynamicCheck(o : Object, n : string, f : Object, m : string)
 reads f, this`objects
 {        m in f.fieldModes &&
          n in o.fieldModes &&
          o.fieldModes[n] == f.fieldModes[m] &&  //field declared types??
          m in f.fields &&
          f.fields[m] in objects &&
          ! o.region.Frozen? && //can't assign into an immutable object
          ! f.region.Frozen? && //oops, can't move OUT of an immutable object either!
          VeniceReferenceOK(o,  f.fields[m]) 
}



predicate betterCopyDynamicCheck(o : Object, n : string, f : Object, m : string)
 reads f, this`objects
  {       m in f.fieldModes &&
          n in o.fieldModes &&
          o.fieldModes[n] == f.fieldModes[m] &&  //field declared types??
          m in f.fields &&
          f.fields[m] in objects &&
          ! o.region.Frozen? && //can't assign into an immutable object
          VeniceReferenceOK(o,  f.fields[m]) &&
          ! f.fieldModes[m].Iso?
  }





  method dynCopy(o : Object, n : string, f : Object, m : string) returns (r : Status)

    requires n != m;  //can't write to oneself field (although o can equal f?) //seems a bit shifty. houjld be fixed.

    requires o  in objects 
    requires f  in objects

    requires Valid()

    //VENICE TODO IS Statically checked - so should get rid of this stuff here
    //or rather; shold get rid of the dynamic checks
    //and incorporate them staticaly in here
    // requires f.fieldModes[m] == Mut;
     //this is the assignment, so need to look at "assignment comaptible" and the paper...



    modifies o`fields
    modifies f`fields
    
    ensures unchanged(this`objects)
    ensures r.Success? ==> (n in o.fields)
    ensures r.Success? ==> old(m in f.fields)
    ensures r.Success? ==> m in f.fields
    ensures r.Success? ==> (o.fields[n] == old(f.fields[m]))
    ensures r.Success? ==> (o.fields[n] == (f.fields[m]))
    ensures r.Success? == old(betterCopyDynamicCheck(o, n, f, m))
    ensures Valid2()
    { 
      reveal Valid();
      reveal o.Valid();
      reveal Valid2(); 

      assert Valid2() ==> Valid();

      if (!betterCopyDynamicCheck(o,n,f,m)) //dynamic check on actual types
             { 
              return Failure("FUCKED2"); } 

      r := Success;

      var value := f.fields[m];

      if (fExists(o,n)) {fNullify(o,n);}


      fInitialise(o,n,value);
    }


//deletes all fields a single iso or mut - should blow away any non-imm object
//if it's a mut, then it could still have incoming pointers...
  method {:timeLimit 30} dynNukeObject(iso : Object) 
    requires iso  in objects
    requires not(iso.region.Frozen?)
   
    requires Valid()

    //modifies ownedBy(objects, iso.region)
    modifies iso`fields
    
    //ensures unchanged(objects - ownedBy(objects, iso.region))
    //  //  ensures forall o <- ownedBy(objects, iso.region) :: o.fields == map[]

    ensures unchanged(objects - {iso})
    ensures iso.fields == map[]
    ensures edges(objects) <= old(edges(objects));
    ensures forall e <- edges(objects) :: (e.f != iso) // && (e.t.region != iso.region)
    ensures Valid2()
    { 
      reveal Valid();
      reveal iso.Valid();
     
      assert heapExternalsZeroOrOne(objects);

      var xedges := edges(objects);
      var xisos := justTheIsos(objects);

      assert heapExternalsZeroOrOne(objects);
      
//      var badEdges := set e <- edges(objects) | (e.f.region == iso.region);

     var badEdges := set e <- edges(objects) | (e.f == iso);

     iso.fields := map[];

      var zedges := edges(objects); 

      RefCountIsMonotonic(xisos,xedges,zedges);

      assert justHeapExternalEdges(zedges) <= justHeapExternalEdges(xedges);
    
      //assert forall i <- xisos :: refCountEdges(i, zedges) <= 1;
      reveal Valid2();

  assume heapExternalsZeroOrOneEdges(zedges); //VENICE TODO FUCKISM

      assert heapExternalsZeroOrOne(objects);
      assert Valid2();
    }
}










//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//
// static move assignment: frame is an object representing a frame
//  does "move" from field f to field t  i.e. frame.t <- frame.f
//   staticMoveAsg(t : string, f : string, frame : Object, memory : Heap)
//  does "shallow copy" from field f to field t  i.e. frame.t := frame.f
//   staticCopyAsg(t : string, f : string, frame : Object, memory : Heap)
//
//  these call the dynamically checked version to do the actually work
//  but their preconditions are all essentially "static" 
//  they they asssert that their result is OK - because the "static types"
//   or capabilitiesr or modes --- prevent any errors.
// 
//  frankly this is probalby belt-and-braces, 

method staticMoveAsg(t : string, f : string, frame : Object, memory : Memory)
  requires frame in memory.objects
  requires f  in frame.fields
  requires t  in frame.fieldModes
  requires f  in frame.fieldModes 
 
  requires memory.Valid()

  requires t != f
  requires frame.fieldModes[t] == frame.fieldModes[f]
  requires not( frame.region.Frozen? )

  modifies frame`fields

  ensures t in frame.fields
  ensures f !in frame.fields
  ensures (frame.fields[t] == old(frame.fields[f]))

  {
    reveal memory.Valid();
    reveal frame.Valid();

    var r := memory.dynMove(frame, t, frame, f);

    assert r.Success?;
  }



//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//
// static copy assignment: frame is an object representing a frame
//   does "copy" from field f to field t
//
method staticCopyAsg(t : string, f : string, frame : Object, memory : Memory)
  requires frame in memory.objects
  requires f  in frame.fields
  requires t  in frame.fieldModes
  requires f  in frame.fieldModes 
 
  requires memory.Valid()

  requires t != f
  requires frame.fieldModes[t] == frame.fieldModes[f]
  requires not( frame.fieldModes[f].Iso? )
  requires not( frame.region.Frozen? )

  modifies frame`fields

  ensures f in frame.fields
  ensures t in frame.fields
  ensures (frame.fields[t] == old(frame.fields[f]))
  {
    reveal memory.Valid();
    reveal frame.Valid();
    reveal memory.Valid2();

    var r := memory.dynCopy(frame, t, frame, f);

    assert r.Success?;
   }





//a random example of proving a global lemma over the memory:
//here that the only things pointed to by immutables are immutables
//talk to kjx for code from vh28i3 which tried to do reachability 
//based on code from Rustan's book

lemma OnlyIMMsOKOutOfImms(h : Memory, i : Object, j : Object)
 requires h.Valid()
 requires i in h.objects
 requires j in h.objects
 requires j in i.outgoing()
 requires i.region.Frozen?
 ensures  j.region.Frozen?
{
    reveal h.Valid();
    reveal i.Valid();
    reveal j.Valid();
}




//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/// NOTES                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


  //TODO 
  //addobjext supporting Isos  - DONE
  //dynamic move assign - DONE
  //dynamic copy assign - DONE
  //DelEdge / Nullify - remove an objects field.  should be fine - DONE
  //Del/Drop Object? - only if the objects refCount is 0?
  //static mov3 assign - DONE
  //static copy assign - DONE
  //dyhamic initialise (i.e. from a newly added object)
  //static initialise - ?
  //can't mutate ISOs - DONE

  //reachability constraints - see vh28i3 for a start...

  //swap semantics (rather than copy or move)
  //freezing-by-cloning (or some other way to initialise imms)
  //model send-to-processes?
  //model stack frames...  ***this is next big thing***

  //could give ALL objects a const pointer to their own memory??
  //have to creat objects by messages to a memory 
  //then could write o.hasField(f), o.readField(f), o.initField(f, o')


  //the raw and the cooked?
  //modelling enter & pausing
  //modelling memory
  //buying vs temporary nullifying etc etc 
  //the gallifrey war = nullification and shit
  //stack vs memory vs appel-stacks unification 
  //modelling deletion & GC properly - how?
  //

//is there enough here or do I need a more "static"  type system?
//
// staging
//  Imms are Imm
//  Isos are actually Iso :-)
//  Muts owned by Isos...
//  Val*ues* (hah hah hah) whot get cloned
//  Enc*aps* - Muts that own things
//  Cown / Down - things that own a MUT
//  Tok*en*? / Rsc  - linear tokens
//
//       immutable     unique     (can own shit)
// Imm       X
// Iso                   X            owns Mut
// Mut      
// Rsc       X           X            
// Enc                                owns Encs?? 

// ALL-PAATH recachqbility (see vh28i3)
// Imms cn only reach Imms
// Isos cna only redach Isons & Imms (Dala)
// etc.  
// 
// Execution in one region does not affect the GC-related properties of another region.
// Where “GC-related” properties are:
//   Reachability from any stack frame
//   Reference count
//
// you can garbage collect (or even reset/purge) one region without changing any other regions
// GCing one region not only doesn't directly modify any other regions,
// it also does not change the reachability status of any other objecty in any other region?
//
// what about Imms? (can't chagne them) 
// what about NESTED Isos?  outgoing pointers.... grrr. 
//
//








//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/// LIBRARY CODE (mostly stolen)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// //more code fro the dafny librayr copied in because copied - dafny.org
  function {:opaque} RemoveKeys<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
    ensures forall x <- m :: (x in xs) != (x in m')
  {
    m - xs
  }

  /* Remove a key-value pair. Returns unmodified map if key is not found. */
  function {:opaque} RemoveKey<X, Y>(m: map<X, Y>, x: X): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, {x})
    ensures |m'.Keys| <= |m.Keys|
    ensures x in m ==> |m'| == |m| - 1
    ensures x !in m ==> |m'| == |m|
    ensures m'.Keys == m.Keys - {x}
    ensures forall x' <- m :: (x == x') != (x' in m')
  {
    var m' := map x' | x' in m && x' != x :: m[x'];
    assert m'.Keys == m.Keys - {x};
    m'
  }



//from the Dafny Library or manual - dafny.org
datatype Status =
| Success
| Failure(error: string)
{
  predicate IsFailure() { this.Failure?  }
  function PropagateFailure(): Status
    requires IsFailure()
  {
    Failure(this.error)
  }
}



predicate not(x : bool) { !x }  //becuase sometimes ! is too hard to see!



//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/// TESTS                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


//some "tests" for want of a better word.
method Main()
{
   var memory := new Memory();

  var i1 := new Object(Isolate, map[] );

  var m1 := new Object(Heap(i1), map[]);

  var x1 := new Object(Frozen, map[] );

  var i2 := new Object(Isolate, map[] );

  var m2 := new Object(Heap(i2), map[]);

  memory.fAddObject(i1);
  memory.fAddObject(m1);
  memory.fAddObject(x1);
  memory.fAddObject(i2);
  // memory.fAddObject(m2);

  // assert   VeniceDeclarationOK(Mode.Imm, Mode.Imm);
  // assert ! VeniceDeclarationOK(Mode.Imm, Mode.Iso);
  // assert ! VeniceDeclarationOK(Mode.Imm, Mode.Mut);

  // assert   VeniceDeclarationOK(Mode.Iso, Mode.Imm);
  // assert   VeniceDeclarationOK(Mode.Iso, Mode.Iso);
  // assert   VeniceDeclarationOK(Mode.Iso, Mode.Mut);

  // assert   VeniceDeclarationOK(Mode.Mut, Mode.Imm);
  // assert   VeniceDeclarationOK(Mode.Mut, Mode.Iso);
  // assert   VeniceDeclarationOK(Mode.Mut, Mode.Mut);




  assert   VeniceReferenceOK(i1, i1); 
  assert   VeniceReferenceOK(i1, m1); 
  assert   VeniceReferenceOK(i1, x1); 
  assert   VeniceReferenceOK(i1, i2); 
  assert ! VeniceReferenceOK(i1, m2); 

  assert   VeniceReferenceOK(m1, i1); 
  assert   VeniceReferenceOK(m1, m1); 
  assert   VeniceReferenceOK(m1, x1); 
  assert   VeniceReferenceOK(m1, i2); 
  assert ! VeniceReferenceOK(m1, m2); 

  assert ! VeniceReferenceOK(x1, i1); 
  assert ! VeniceReferenceOK(x1, m1); 
  assert   VeniceReferenceOK(x1, x1); 
  assert ! VeniceReferenceOK(x1, i2); 
  assert ! VeniceReferenceOK(x1, m2); 

  assert   VeniceReferenceOK(i2, i1); 
  assert ! VeniceReferenceOK(i2, m1); 
  assert   VeniceReferenceOK(i2, x1); 
  assert   VeniceReferenceOK(i2, i2); 
  assert   VeniceReferenceOK(i2, m2); 

  assert   VeniceReferenceOK(m2, i1); 
  assert ! VeniceReferenceOK(m2, m1); 
  assert   VeniceReferenceOK(m2, x1); 
  assert   VeniceReferenceOK(m2, i2); 
  assert   VeniceReferenceOK(m2, m2);

}


///more 'tests"
method Main1() {
  var memory := new Memory();

  var i1 := new Object(Isolate, map["x1" := Mode.Mut] );
  var i2 := new Object(Isolate, map["x2" := Mode.Mut] );

  var m1 := new Object(Heap(i1), map[]);
  
  memory.fAddObject(i1);
  memory.fAddObject(i2);

  memory.fAddObject(m1);
  memory.fInitialise(i1,"x1",m1);

  var r := memory.dynCopy(i1, "x1", i2, "x2");

  assert not(r.Success?);

}

