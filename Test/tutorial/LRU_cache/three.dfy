datatype Outcome<T> =
	| Success(value: T)
	| Failure

datatype entry<T(!new,==)> = Entry(key: nat,value: T)
	
datatype Ref<T> =
	| Alloc(deref: T)
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

	predicate Invariant()
		reads this, Repr
	{

		// Dynamic frame properties
		&& (forall key: nat :: key in cache ==> cache[key] in Repr)
		&& (cache_head.Alloc? ==> cache_head.deref in Repr)
		&& (cache_tail.Alloc? ==> cache_tail.deref in Repr)
		&& (forall i: Item :: i in Repr ==> i.more_recently_used.Null? || i.more_recently_used.deref in Repr)
		&& (forall i: Item :: i in Repr ==> i.less_recently_used.Null? || i.less_recently_used.deref in Repr)
		
		// Functional properties
		&& (forall key: nat :: key in cache ==> key in storage)
		&& (forall key: nat :: key in cache ==> cache[key].key == key)
		&& (forall key: nat :: key in cache ==> cache[key].value == storage[key])
		&& (forall key, key': nat :: key in cache && key' in cache && key != key' ==> cache[key] != cache[key'])

		// Structural properties
		&& (|cache| == 0 <==> Repr == {})
		&& (|cache| == 0 <==> cache_head == cache_tail == Null)
		&& (|cache| == 1 ==> (cache_head == cache_tail && cache_head.Alloc?))
		&& (cache_head.Alloc? ==> cache_head.deref.more_recently_used.Null?)
		&& (cache_tail.Alloc? ==> cache_tail.deref.less_recently_used.Null?)
		&& (|cache| == 1 ==> Repr == {cache_head.deref})
		&& (|cache| >= 1 <==> cache_head.Alloc? && cache_tail.Alloc?)
		&& (|cache| >= 2 ==> cache_head != cache_tail)
		&& (|cache| >= 2 ==> cache_head.deref.less_recently_used.Alloc?)
		&& (|cache| >= 2 ==> cache_tail.deref.more_recently_used.Alloc?)
		
		// && |old(cache)| <= |cache| that would be nice but require twostate and then it "spreads"

		
		
		
		

		&& (forall i: Item :: i in Repr ==> (i.more_recently_used.Alloc? && i.less_recently_used.Alloc? <==> Alloc(i) != cache_head && Alloc(i) != cache_tail))
		

		//&& (|cache| == 1 ==> (cache_head == cache_tail && cache_head.Alloc?))
		//&& (|cache| == 1 <== (cache_head == cache_tail && cache_head.Alloc?))
		//&& (|cache| >= 2 ==> cache_head != cache_tail)
		//&& (|cache| >= 2 <== cache_head != cache_tail)
		//&& (|cache| >= 2 <==> cache_head != cache_tail)
		
		
		//&& (cache_head.Some? ==> cache_head.value.more_recently_used.None?)
		//&& (cache_tail.Some? ==> cache_tail.value.less_recently_used.None?)
		//&& (forall i: Item :: i in Repr && Some(i) != cache_head ==> i.more_recently_used.Some?)
		// && (forall i: Item :: i in Repr && Some(i) != cache_tail ==> i.less_recently_used.Some?)
		//&& (forall i: Item :: i in Repr && i.more_recently_used.Some? ==> i.more_recently_used.value.less_recently_used == Some(i))
		//&& (forall i: Item :: i in Repr && i.less_recently_used.Some? ==> i.less_recently_used.value.more_recently_used == Some(i))

		//&& (|cache| >= 2 <==> cache_head != cache_tail)

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

	// method promote(key: nat)
	// 	modifies this, Repr
	// 	requires key in cache
	// 	requires Invariant()
	// 	ensures Invariant()
	// 	//ensures cache_head.Some? ==> cache_head.value.key == key
	// {
	// 	var item := cache[key];
	// 	if |cache| >= 2 {
	// 		if item.more_recently_used.Alloc? {
	// 			if item.less_recently_used.Alloc? {
	// 				assert (cache_tail.Alloc? ==> cache_tail.deref.less_recently_used.Null?);
	// 				//assert (|cache| == 1 <== (cache_head == cache_tail && cache_head.Alloc?));
	// 				item.more_recently_used.deref.less_recently_used := item.less_recently_used;
	// 				item.less_recently_used.deref.more_recently_used := item.more_recently_used;
	// 				cache_head.deref.less_recently_used := Alloc(item);
	// 				item.less_recently_used := cache_head;
	// 				item.more_recently_used := Null;
	// 				cache_head := Alloc(item);

	// 				assume (cache_tail.Alloc? ==> cache_tail.deref.less_recently_used.Null?);
	// 				//assume false;
	// 			} else {
	// 				//assert |cache| >= 2 ==> cache_head != cache_tail;
	// 				cache_tail := item.more_recently_used;
	// 				cache_tail.deref.less_recently_used := Null;
	// 				//item.more_recently_used.value.less_recently_used := None;
	// 				cache_head.deref.less_recently_used := Alloc(item);
	// 				var old_cache_head := cache_head;
	// 				cache_head := Alloc(item);
	// 				cache_head.deref.less_recently_used := old_cache_head;
	// 				cache_head.deref.more_recently_used := Null;
					
	// 				assume false;
	// 			}
	// 		}
	// 	}
	// 	// useful for debugging
	// 	assert |old(cache)| == |cache|;
	// 	assert |old(Repr)| == |Repr|;
	// }
	
	method put_cache(key: nat, value: T)
		modifies this, Repr
		requires key in storage   // Very convenient because this is known from the calling context
		requires storage[key] == value
		requires key !in cache
		requires Invariant()
		ensures Invariant()
	{

		if |cache| == 0 {
			var item: Item := new Item(key,value);
			Repr := Repr + {item};
			cache := cache[key := item];
			cache_head := Alloc(item);
			cache_tail := Alloc(item);
		} else if |cache| == 1 {
			
			var item: Item := new Item(key,value);
			cache := cache[key := item];
			
			Repr := Repr + {item};
			cache_head := Alloc(item);
			cache_head.deref.less_recently_used := cache_tail;
			cache_tail.deref.more_recently_used := cache_head;

			//assert cache_head.deref.more_recently_used.Null?;
			//assert cache_tail.deref.less_recently_used.Null?;
			
			//assert (forall i: Item :: i in Repr ==> (i.more_recently_used.Alloc? && i.less_recently_used.Alloc? ==> Alloc(i) != cache_head && Alloc(i) != cache_tail));
			//assert (forall i: Item :: i in Repr ==> (i.more_recently_used.Alloc? && i.less_recently_used.Alloc? <== Alloc(i) != cache_head && Alloc(i) != cache_tail));
			
			
		} else {
			
			var item: Item := new Item(key,value);
			cache := cache[key := item];
			
			assert (forall i: Item :: i in Repr ==> (i.more_recently_used.Alloc? && i.less_recently_used.Alloc? <==> Alloc(i) != cache_head && Alloc(i) != cache_tail));
			assert cache_head != cache_tail;
			Repr := Repr + {item};
			var old_cache_head := cache_head;
			assert old_cache_head != cache_tail;
			item.less_recently_used := cache_head;
			old_cache_head.deref.more_recently_used := Alloc(item);
			cache_head := Alloc(item);

			assert (forall i: Item :: i in Repr ==> (i.more_recently_used.Alloc? && i.less_recently_used.Alloc? ==> Alloc(i) != cache_head && Alloc(i) != cache_tail));
			
			assert (forall i: Item :: i in Repr ==> (i.more_recently_used.Alloc? && i.less_recently_used.Alloc? <== Alloc(i) != cache_head && Alloc(i) != cache_tail)) by {
				forall i: Item ensures i in Repr ==> (i.more_recently_used.Alloc? && i.less_recently_used.Alloc? <== Alloc(i) != cache_head && Alloc(i) != cache_tail) {
					if i in Repr {
						if  Alloc(i) != cache_head && Alloc(i) != cache_tail {
							if Alloc(i) == old_cache_head {
								//assume i.more_recently_used.Alloc? && i.less_recently_used.Alloc?;

								// It is only thanks to this proof that I figured out the invariants:
								//&& (|cache| >= 2 ==> cache_head.deref.less_recently_used.Alloc?)
								//&& (|cache| >= 2 ==> cache_tail.deref.more_recently_used.Alloc?)
								// that were necessary
							} else {
								assert true;
							}
						}
					}
				}
			}
			
			//assume false;
		}
		
		//assume false;

		// Will do eviction later
		
		// if |cache| == cache_size {
		// 	if cache_tail.None? {
		// 		// Cannot happen
		// 	} else {
		// 		if cache_tail.value.more_recently_used.None? {
		// 			// Cannot happen
		// 		} else {
		// 			var previous_item: Option<Item> := cache_tail.value.more_recently_used;
		// 			if previous_item.None? {
		// 				// Cannot happen 
		// 			} else {
		// 				previous_item.value.less_recently_used := None;
		// 				cache := cache - {previous_item.value.key};
		// 				Repr := Repr - {previous_item.value};
		// 				cache_tail := previous_item;
		// 			}
		// 		}
		// 	}
		// }

			
		
	}

	// Step 1: put, get, no promotion, no eviction
	
	method get(key: nat) returns (result: Outcome<T>)
		modifies this, Repr
		requires Invariant()
		ensures Invariant()
	{
		if key in cache {
			result := Success(cache[key].value);
			//promote(key);
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
