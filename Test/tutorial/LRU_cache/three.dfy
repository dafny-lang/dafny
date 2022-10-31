datatype Outcome<T> =
	| Success(value: T)
	| Failure

datatype entry<T> = Entry(key: nat,value: T)
	
// trait Storage<T(!new,==)> {

// 	ghost var log: seq<entry<T>>

// 	function last_occurence_pre(key: nat, log': seq<entry<T>>): Outcome<T> {
// 		var size: nat := |log'|;
// 		if size == 0 then
// 			Failure
// 		else
// 			var candidate: entry := log'[size-1];
// 			if candidate.key == key then
// 				Success(candidate.value)
// 			else
// 				last_occurence_pre(key, log'[..(size-1)])
// 	}

// 	function last_occurence(key: nat): Outcome<T>
// 		reads this
// 	{
// 		last_occurence_pre(key,log)
// 	}
	
// 	predicate Invariant()
// 		reads this

// 	method get(key: nat) returns (result: Outcome<T>)
// 		requires Invariant()
// 		ensures Invariant()
// 		ensures result.Success? <==> exists index: nat :: index < |log| && log[index].key == key 
// 		ensures result.Success? ==> last_occurence(key).Success? && last_occurence(key).value == result.value
		
// 	function method fget(key: nat): Outcome<T>
//  		reads this
// 		requires Invariant()
		
// 	method put(key: nat, value: T)
// 	 	modifies this
// 		requires Invariant()
// 		ensures log == old(log) + [Entry(key,value)]
// 		ensures Invariant()
		
// }

datatype Option<T> =
	| Some(value: T)
	| None

class Item<T> {

	var more_recently_used: Option<Item<T>>
	var less_recently_used: Option<Item<T>>
	const key: nat
	const value: T

		
	constructor(key: nat, value: T) {

		this.key := key;
		this.value := value;
		more_recently_used := None;
		less_recently_used := None;
		
	}
	
}

class MapStorage<T(!new,==)> {

	ghost var Repr: set<Item<T>>;

	ghost var log: seq<entry<T>>

	function last_occurence_pre(key: nat, log': seq<entry<T>>): Outcome<T> {
		var size: nat := |log'|;
		if size == 0 then
			Failure
		else
			var candidate: entry := log'[size-1];
			if candidate.key == key then
				Success(candidate.value)
			else
				last_occurence_pre(key, log'[..(size-1)])
	}

	function last_occurence(key: nat): Outcome<T>
		reads this
	{
		last_occurence_pre(key,log)
	}
	
	var storage: map<nat,T>

	const cache_size: nat
		
	var cache_head: Option<Item<T>>
	var cache_tail: Option<Item<T>>
	var cache_map: map<nat,Item<T>>

	predicate Invariant()
		reads this, Repr
	{
		&& (forall key: nat :: key in storage <==> exists index: nat :: index < |log| && log[index].key == key)
		&& (forall key: nat :: forall value: T :: (key in storage && storage[key] == value) ==> last_occurence(key).Success? && last_occurence(key).value == value)
		&& (forall key: nat :: key in cache_map ==> cache_map[key] in Repr)
		&& (cache_head.Some? ==> cache_head.value in Repr)
		&& (cache_tail.Some? ==> cache_tail.value in Repr)
		&& (forall i: Item :: i in Repr && i.more_recently_used.Some? ==> i.more_recently_used.value in Repr)
		&& (forall i: Item :: i in Repr && i.less_recently_used.Some? ==> i.less_recently_used.value in Repr)
	}
	
	constructor(size: nat)
		ensures Invariant()
	{
		cache_size := size;
		storage := map[];
		log := [];
		cache_head := None;
		cache_tail := None;
		cache_map := map[];
		Repr := {};
	}

	method promote(item: Item)
		requires Invariant()
		ensures Invariant()

	method evict()
		requires Invariant()
		modifies this, Repr
		ensures Invariant()
	{
		if |cache_map| == cache_size {
			if cache_tail.None? {
				// Cannot happen
			} else {
				if cache_tail.value.more_recently_used.None? {
					// Cannot happen
				} else {
					var previous_item: Option<Item> := cache_tail.value.more_recently_used;
					if previous_item.None? {
						// Cannot happen 
					} else {
						previous_item.value.less_recently_used := None;
						cache_map := cache_map - {previous_item.value.key};
						Repr := Repr - {previous_item.value};
						cache_tail := previous_item;
						assume false;
					}
				}
			}
		}	
	}

	method introduce(key: nat, value: T)
		requires Invariant()
		modifies this
		ensures Invariant()
	{
		var item: Item := new Item(key,value);
		item.less_recently_used := cache_head;
		cache_map := cache_map[key := item];
		cache_head := Some(item);
		Repr := Repr + {item};
		assume false;
	}
	
	method get(key: nat) returns (result: Outcome<T>)
		modifies this, Repr
		requires Invariant()
		ensures Invariant()
		ensures result.Success? <==> exists index: nat :: index < |log| && log[index].key == key
		ensures result.Success? ==> last_occurence(key).Success? && last_occurence(key).value == result.value
	{
		if key in cache_map {
			result := Success(cache_map[key].value);
			promote(cache_map[key]);
			assume false;
		} else if key in storage {
			var value: T := storage[key];
			result := Success(value);
			evict();
			introduce(key,value);
			assume false;
		} else {
			result := Failure;
		}
	}

	method put(key: nat, value: T)
		modifies this
		requires Invariant()
		ensures log == old(log) + [Entry(key,value)]
		ensures Invariant()
	{

		assert forall key: nat :: key in storage <==> exists index: nat :: index < |log| && log[index].key == key;

		storage := storage[key := value];

		assert forall key: nat :: key in old(storage) <==> exists index: nat :: index < |log| && log[index].key == key;

		log := log + [Entry(key,value)];

		assert forall key: nat :: key in old(storage) <==> exists index: nat :: index < |old(log)| && old(log)[index].key == key;

		forall key': nat ensures key' in storage ==> exists index: nat :: index < |log| && log[index].key == key' {
			if key' in storage {
				if key == key' {
					var index: nat := |log| - 1;
					assert log[index].key == key;
				} else {
					assert key' in old(storage);
					var index: nat :| index < |old(log)| && old(log)[index].key == key';
					assert log[index].key == old(log)[index].key;
				}
			}
		}
	}

	function method fget(key: nat): Outcome<T>
		reads this, Repr
		requires Invariant()
	{
		if key in storage then Success(storage[key]) else Failure
	}
	
	lemma prop_test_1(key: nat)
		requires Invariant()
		requires fget(key).Success?
		ensures exists index: nat :: index < |log| && log[index].key == key
		ensures last_occurence(key).Success? && last_occurence(key).value == fget(key).value
	{
	}

}
