datatype Outcome<T> =
	| Success(value: T)
	| Failure

datatype entry<T(!new,==)> = Entry(key: nat,value: T)
	
datatype Option<T> =
	| Some(value: T)
	| None

class Item<T(!new,==)> {
	
	var more_recently_used: Option<Item<T>>
	var less_recently_used: Option<Item<T>>
	const key: nat
	var value: T

	constructor(key: nat, value: T)
		ensures this.key == key
		ensures this.value == value
		ensures this.more_recently_used == None
		ensures this.less_recently_used == None
	{

		this.key := key;
		this.value := value;
		more_recently_used := None;
		less_recently_used := None;

	}
	
}

class LRUCache<T(!new,==)> {

	ghost var Repr: set<Item<T>>;
	
	var storage: map<nat,T>

	const cache_size: nat
		
	var cache_head: Option<Item<T>>
	var cache_tail: Option<Item<T>>
	var cache: map<nat,Item<T>>

	predicate Invariant()
		reads this, Repr
	{
		&& (forall key: nat :: key in cache ==> key in storage)
		&& (forall key: nat :: key in cache ==> cache[key] in Repr)
		&& (forall key: nat :: key in cache ==> cache[key].key == key)
		&& (forall key: nat :: key in cache ==> cache[key].value == storage[key])
		&& (cache_head.Some? ==> cache_head.value in Repr)
		&& (cache_tail.Some? ==> cache_tail.value in Repr)
		&& (forall i: Item :: i in Repr ==> i.more_recently_used.None? || i.more_recently_used.value in Repr)
		&& (forall i: Item :: i in Repr ==> i.less_recently_used.None? || i.less_recently_used.value in Repr)
		&& (forall key, key': nat :: key in cache && key' in cache && key != key' ==> cache[key] != cache[key'])
		&& (cache_head.Some? ==> cache_head.value.more_recently_used.None?)
		&& (cache_tail.Some? ==> cache_tail.value.less_recently_used.None?)
		&& (forall i: Item :: i in Repr && Some(i) != cache_head ==> i.more_recently_used.Some?)
		&& (forall i: Item :: i in Repr && Some(i) != cache_tail ==> i.less_recently_used.Some?)
		&& (forall i: Item :: i in Repr && i.more_recently_used.Some? ==> i.more_recently_used.value.less_recently_used == Some(i))
		&& (forall i: Item :: i in Repr && i.less_recently_used.Some? ==> i.less_recently_used.value.more_recently_used == Some(i))
		&& (|cache| == 0 ==> cache_head == cache_tail == None)
		&& (|cache| == 1 ==> cache_head == cache_tail)
		&& (|cache| >= 1 ==> cache_head.Some? && cache_tail.Some?)
		&& (|cache| >= 2 <==> cache_head != cache_tail)

	}
	
	constructor(size: nat)
		requires size >= 2
		ensures Invariant()
	{
		cache_size := size;
		storage := map[];
		cache_head := None;
		cache_tail := None;
		cache := map[];
		Repr := {};
	}

	method promote(key: nat)
		modifies this, Repr
		requires key in cache
		requires Invariant()
		ensures Invariant()
		//ensures cache_head.Some? ==> cache_head.value.key == key
	{
		var item := cache[key];
		if |cache| >= 2 {
			if item.more_recently_used.Some? {
				if item.less_recently_used.Some? {
					assert cache_tail.value.less_recently_used.None?;
					item.more_recently_used.value.less_recently_used := item.less_recently_used;
					//assert cache_tail.value.less_recently_used.None?;
					item.less_recently_used.value.more_recently_used := item.more_recently_used;
					cache_head.value.less_recently_used := Some(item);
					item.less_recently_used := cache_head;
					item.more_recently_used := None;
					cache_head := Some(item);
					//assume false;
				} else {
					
					//assert |cache| >= 2 ==> cache_head != cache_tail;
					cache_tail := item.more_recently_used;
					cache_tail.value.less_recently_used := None;
					//item.more_recently_used.value.less_recently_used := None;
					cache_head.value.less_recently_used := Some(item);
					var old_cache_head := cache_head;
					cache_head := Some(item);
					cache_head.value.less_recently_used := old_cache_head;
					cache_head.value.more_recently_used := None;
					assume false;
				}
			}
		}
	}
	
	method put_cache(key: nat, value: T)
		modifies this, Repr
		requires key in storage   // Very convenient because this is known from the calling context
		requires storage[key] == value
		requires key !in cache
		requires Invariant()
		ensures Invariant()
	{

		var item: Item := new Item(key,value);
		Repr := Repr + {item};
		
		if |cache| == 0 {
			cache := cache[key := item];
			cache_head := Some(item);
			cache_tail := Some(item);
		} else {
			item.less_recently_used := cache_head;
			cache := cache[key := item];
			cache_head.value.more_recently_used := Some(item);
			cache_head := Some(item);
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
	
	method get(key: nat) returns (result: Outcome<T>)
		modifies this, Repr
		requires Invariant()
		ensures Invariant()
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
		//assert forall key': nat :: key' in cache ==> cache[key'].value == storage[key'];

		storage := storage[key := value];

		//assert forall key': nat :: key' in cache && key' != key ==> cache[key'].value == storage[key'];
		//assert forall key': nat :: key' in cache ==> cache[key'].value == old(storage)[key'];

		if key in cache {
			cache[key].value := value;
			assert cache[key].value == storage[key];
			// assert forall key': nat :: key' != key && key' in cache ==> cache[key'].value == storage[key'] by {
			// 	forall key': nat ensures key' != key && key' in cache ==> cache[key'].value == storage[key'] {
			// 		if key' != key && key' in cache {
			// 			assert cache[key'].value == old(cache)[key'].value;
			// 			assert storage[key'] == old(storage)[key'];
			// 			// Aliasing!
			// 			assert old(cache)[key'].value == old(cache[key'].value);
			// 			assert old(cache[key'].value) == old(storage)[key'];
			// 		}
			// 	}
			// }
		}
	}

}
