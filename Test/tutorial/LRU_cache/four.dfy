datatype Outcome<T> =
	| Success(value: T)
	| Failure

datatype entry<T(!new,==)> = Entry(key: nat,value: T)
	
datatype Ref<T> =
	| Ptr(deref: T)
	| Null

class Item<T(!new,==)> {
	
	var more_recently_used: Ref<Item<T>>
	var less_recently_used: Ref<Item<T>>
	const key: nat
	var value: T

	constructor(key: nat, value: T)
		ensures this.key == key
		ensures this.value == value
		ensures this.more_recently_used == Null
		ensures this.less_recently_used == Null
	{

		this.key := key;
		this.value := value;
		more_recently_used := Null;
		less_recently_used := Null;

	}
	
}

class LRUCache<T(!new,==)> {

	ghost var Repr: set<Item<T>>;
	
	var storage: map<nat,T>

	const cache_size: nat
		
	var cache_head: Ref<Item<T>>
	var cache_tail: Ref<Item<T>>
	var cache: map<nat,Item<T>>

	// lemma test1(i: Item<T>, i': Item<T>)
	// 	requires i in Repr
	// 	requires i' in Repr
	// 	requires i != i'
	// 	requires forall key: nat :: key in cache ==> cache[key] in Repr
	// 	requires forall key: nat :: key in cache ==> cache[key].key == key
	// 	requires forall key, key': nat :: key in cache && key' in cache && key != key' ==> cache[key] != cache[key']
	// 	requires |cache| == |Repr|
	// 	ensures i.key != i'.key
	//{
	//}
	// If X and Y are finite and same number of elements then f is injective iff f is surjective
	// in conclusion, it is bijective

	lemma test1(i: Item<T>)
		requires i in Repr
		requires forall key, key': nat :: key in cache && key' in cache && key != key' ==> cache[key] != cache[key']
		requires |cache| == |Repr|
		ensures exists key: nat :: key in cache && cache[key] == i
		
	lemma test2(i: Item<T>)
		requires i in Repr
		requires forall key: nat :: key in cache ==> cache[key] in Repr
		requires forall key: nat :: key in cache ==> cache[key].key == key
		requires forall key, key': nat :: key in cache && key' in cache && key != key' ==> cache[key] != cache[key']
		requires |cache| == |Repr|
		ensures i.key in cache
		ensures cache[i.key] == i
	{
		test1(i);
		var key: nat :| key in cache && cache[key] == i;
	}

	lemma foo<T>(e: T, S: set<T>)
		requires e in S
		ensures |S - {e}| == |S| - 1
	
	predicate Invariant()
		reads this, Repr
	{

		&& cache_size >= 2 
		
		// Dynamic frame properties
		&& (forall key: nat :: key in cache ==> cache[key] in Repr)
		&& (cache_head.Ptr? ==> cache_head.deref in Repr)
		&& (cache_tail.Ptr? ==> cache_tail.deref in Repr)
		//&& (forall i: Item :: i in Repr ==> cache[i.key] == i)
		&& (forall i: Item :: i in Repr ==> i.more_recently_used.Null? || i.more_recently_used.deref in Repr)
		&& (forall i: Item :: i in Repr ==> i.less_recently_used.Null? || i.less_recently_used.deref in Repr)
		
		// Functional properties
		&& (forall key: nat :: key in cache ==> key in storage)
		&& (forall key: nat :: key in cache ==> cache[key].key == key)
		&& (forall key: nat :: key in cache ==> cache[key].value == storage[key])
		&& (forall key, key': nat :: key in cache && key' in cache && key != key' ==> cache[key] != cache[key'])

		// Structural properties
		//&& (|cache| <= cache_size)
		//&& (cache_head.Ptr? ==> cache_head.deref.key in cache)
		//&& (cache_tail.Ptr? ==> cache_tail.deref.key in cache)
		&& (|cache| == |Repr|)
		&& (|cache| == 0 <==> cache_head == cache_tail == Null)
		&& (|cache| == 1 ==> (cache_head == cache_tail && cache_head.Ptr?))
		&& (cache_head.Ptr? ==> cache_head.deref.more_recently_used.Null?)
		&& (cache_tail.Ptr? ==> cache_tail.deref.less_recently_used.Null?)
		&& (|cache| == 1 ==> Repr == {cache_head.deref})
		&& (|cache| >= 1 <==> cache_head.Ptr? && cache_tail.Ptr?)
		&& (|cache| >= 2 ==> cache_head != cache_tail)
		&& (|cache| >= 2 ==> cache_head.deref.less_recently_used.Ptr?)
		&& (|cache| >= 2 ==> cache_tail.deref.more_recently_used.Ptr?)
		&& (forall i: Item :: i in Repr ==> (i.more_recently_used.Ptr? && i.less_recently_used.Ptr? <==> Ptr(i) != cache_head && Ptr(i) != cache_tail))
		&& (forall i: Item :: i in Repr ==> (i.more_recently_used.Null? <==> Ptr(i) == cache_head))
		&& (forall i: Item :: i in Repr ==> (i.less_recently_used.Null? <==> Ptr(i) == cache_tail))
		&& (forall i: Item :: i in Repr ==> i.less_recently_used.Null? ||  i.less_recently_used.deref.more_recently_used == Ptr(i))
		&& (forall i: Item :: i in Repr ==> i.more_recently_used.Null? || i.more_recently_used.deref.less_recently_used == Ptr(i))
		&& (|cache| == 1 <== (cache_head == cache_tail && cache_head.Ptr?))
		&& (|cache| >= 2 <== cache_head != cache_tail)

	}
	
	constructor(size: nat)
		requires size >= 2
		ensures Invariant()
	{
		cache_size := size;
		storage := map[];
		cache_head := Null;
		cache_tail := Null;
		cache := map[];
		Repr := {};
	}

	// We could do better with a log and prove that the order in the DLL correspond to the log
	method promote(key: nat)
		modifies this, Repr
		requires key in cache
		requires Invariant()
		ensures Invariant()
		//ensures |cache| >= 2 ==> cache_head.deref.key == key 
		ensures storage == old(storage)
	{
		var item := cache[key];
		if |cache| >= 2 {
			if item.more_recently_used.Ptr? {
				if item.less_recently_used.Ptr? {

					// Get item out of the DLL
					item.more_recently_used.deref.less_recently_used := item.less_recently_used;
					item.less_recently_used.deref.more_recently_used := item.more_recently_used;
					// Swap cache head
					var old_cache_head := cache_head;
					item.less_recently_used := old_cache_head;
					item.more_recently_used := Null;
					cache_head := Ptr(item);
					old_cache_head.deref.more_recently_used := cache_head;
					
				} else {

					// Get item out of the DLL and fix cache_tail
					cache_tail := item.more_recently_used;
					cache_tail.deref.less_recently_used := Null;
					var old_cache_head := cache_head;
					item.less_recently_used := old_cache_head;
					item.more_recently_used := Null;
					cache_head := Ptr(item);
					old_cache_head.deref.more_recently_used := cache_head;
					
				}
			}
		}
	}
	
	method put_cache(key: nat, value: T)
		modifies this, Repr
		requires key in storage   
		requires storage[key] == value
		requires key !in cache
		requires Invariant()
		ensures Invariant()
		ensures storage == old(storage)
	{

		if |cache| == 0 {
			
			var item: Item := new Item(key,value);
			Repr := Repr + {item};
			cache := cache[key := item];
			cache_head := Ptr(item);
			cache_tail := Ptr(item);
			
		} else if |cache| == 1 {
			
			var item: Item := new Item(key,value);
			cache := cache[key := item];		
			Repr := Repr + {item};
			cache_head := Ptr(item);
			cache_head.deref.less_recently_used := cache_tail;
			cache_tail.deref.more_recently_used := cache_head;

		} else {
			
			var item: Item := new Item(key,value);
			cache := cache[key := item];
			Repr := Repr + {item};
			var old_cache_head := cache_head;
			assert old_cache_head != cache_tail;
			item.less_recently_used := cache_head;
			old_cache_head.deref.more_recently_used := Ptr(item);
			cache_head := Ptr(item);

		}

		if |cache| == cache_size + 1 {
			// Need to evict

			var old_cache_tail := cache_tail; 
			cache_tail := old_cache_tail.deref.more_recently_used;
			cache_tail.deref.less_recently_used := Null;

			test2(old_cache_tail.deref);
			assert old_cache_tail.deref.key in cache;
			//assert cache[old_cache_tail.deref.key] == old_cache_tail.deref; 

			assert |Repr| == |cache|;
			assert old_cache_tail.deref in Repr;
			Repr := Repr - {old_cache_tail.deref};

			assume |Repr| == |old(Repr)| - 1; 
			
			cache := cache - {old_cache_tail.deref.key};

			assert |cache| == |old(cache)| - 1;
			
		}
		
	}
	
	method get(key: nat) returns (result: Outcome<T>)
		modifies this, Repr
		requires Invariant()
		ensures Invariant()
		ensures key in storage ==> result.Success? && result.value == storage[key]
		ensures result.Failure? ==> key !in storage
	{
		if key in cache {
			result := Success(cache[key].value);
			promote(key);
		} else if key in storage {
			var value: T := storage[key];
			result := Success(value);
			put_cache(key,value);
		} else {
			result := Failure;
		}
	}

	method put(key: nat, value: T)
		modifies this, Repr
		requires Invariant()
		ensures Invariant()
	{
		storage := storage[key := value];
		if key in cache {
			cache[key].value := value;
			assert cache[key].value == storage[key];
		}
	}

}
