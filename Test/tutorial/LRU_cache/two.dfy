datatype Outcome<T> =
	| Success(value: T)
	| Failure

datatype entry<T> = Entry(key: nat,value: T)
	
trait Storage<T(!new)> {

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
	
	predicate Invariant()
		reads this

	method get(key: nat) returns (result: Outcome<T>)
		requires Invariant()
		ensures Invariant()
		ensures result.Success? <==> exists index: nat :: index < |log| && log[index].key == key 
		ensures result.Failure? <==> !exists index: nat :: index < |log| && log[index].key == key
		ensures result.Success? ==> last_occurence(key).Success? && last_occurence(key).value == result.value
		
	function method fget(key: nat): Outcome<T>
 		reads this
		requires Invariant()
		
	method put(key: nat, value: T)
	 	modifies this
		requires Invariant()
		ensures log == old(log) + [Entry(key,value)]
		ensures Invariant()
		
}

class MapStorage<T(!new)> extends Storage<T> {

	var storage: map<nat,T>
		
	predicate Invariant()
		reads this
	{
		&& (forall key: nat :: key in storage <==> exists index: nat :: index < |log| && log[index].key == key)
		&& (forall key: nat :: forall value: T :: (key in storage && storage[key] == value) ==> last_occurence(key).Success? && last_occurence(key).value == value)
	}
	
	constructor()
		ensures Invariant()
	{
		storage := map[];
		log := [];
	}

	method get(key: nat) returns (result: Outcome<T>)
		requires Invariant()
		ensures Invariant()
		ensures result.Success? <==> exists index: nat :: index < |log| && log[index].key == key
		ensures result.Failure? <==> !exists index: nat :: index < |log| && log[index].key == key
		ensures result.Success? ==> last_occurence(key).Success? && last_occurence(key).value == result.value
	{
		if key in storage {
			result := Success(storage[key]);
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
		reads this
		requires Invariant()
	{
		if key in storage then Success(storage[key]) else Failure
	}
	
	lemma prop_test_1(key: nat)
		requires Invariant()
		requires fget(key).Success?
		ensures exists index: nat :: index < |log| && log[index].key == key
	{
	}

}
