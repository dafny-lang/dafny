datatype Outcome<T> =
	| Success(value: T)
	| Failure

datatype entry<T> = Entry(key: nat,value: T)

// There are different approaches to the formalization

// One possibility is to define the log so that it contains the trace of all operations
// Then the properties are "intemporal": you can say, at any index, if the entry is a get
// then ...

	
trait Storage<T(!new)> {

	ghost var log: seq<entry<T>>
	
	// function method get(key: nat): Outcome<T>
	// 	reads this
		
	// method put(key: nat, value: T)
	// 	modifies this
	// 	ensures log == old(log) + [Entry(key,value)]

	// lemma prop1(key: nat, result: Outcome<T>)
	// 	requires get(key) == result
	// 	requires result.Success?
	// 	ensures exists index: nat :: index < |log| && log[index] == Entry(key,result.value) && (forall index': nat :: index' > index && index' < |log| ==> log[index'].key != key)

	// lemma prop2(key: nat)
	// 	requires get(key).Failure?
	// 	ensures forall index: nat :: index < |log| ==> log[index].key != key
		
}

class MapStorage<T(!new)> extends Storage<T> {

	var storage: map<nat,T>

	predicate InSync()
		reads this
	{
		forall key: nat :: key in storage ==> exists index: nat :: index < |log| && log[index].key == key
	}
	
	constructor()
		ensures InSync()
	{
		storage := map[];
		log := [];
	}

	method get1(key: nat) returns (result: Outcome<T>)
		requires InSync()
		ensures InSync()
		ensures result.Success? ==> exists index: nat :: index < |log| && log[index].key == key
	{
		if key in storage {
			result := Success(storage[key]);
			//ghost var index: nat :| index < |log| && log[index].key == key;
		} else {
			result := Failure;
		}
	}
	
	function method get2(key: nat): Outcome<T>
		reads this
	{
		if key in storage then Success(storage[key]) else Failure
	}

	method put(key: nat, value: T)
		modifies this
		requires InSync()
		ensures log == old(log) + [Entry(key,value)]
		ensures InSync()
	{

		assert forall key: nat :: key in storage ==> exists index: nat :: index < |log| && log[index].key == key;

		storage := storage[key := value];

		assert forall key: nat :: key in old(storage) ==> exists index: nat :: index < |log| && log[index].key == key;

		log := log + [Entry(key,value)];

		assert forall key: nat :: key in old(storage) ==> exists index: nat :: index < |old(log)| && old(log)[index].key == key;

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

	// lemma test(key: nat, result: Outcome<T>)
	// 	requires get2(key) == result
	// 	requires result.Success?
	// 	ensures exists index: nat :: index < |log| && log[index].key == key
	// {
		
	// }
	
	// lemma prop1(key: nat, result: Outcome<T>)
	// 	requires get(key) == result
	// 	requires result.Success?
	// 	ensures exists index: nat :: index < |log| && log[index] == Entry(key,result.value) && (forall index': nat :: index' > index && index' < |log| ==> log[index'].key != key)
		
	// lemma prop2(key: nat)
	// 	requires get(key).Failure?
	// 	ensures forall index: nat :: index < |log| ==> log[index].key != key

}
