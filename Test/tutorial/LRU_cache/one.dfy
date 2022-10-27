datatype Outcome<T> =
| Success(value: T)
| Failure

trait Storage<T> {

	method get(key: nat) returns (result: Outcome<T>)
	method put(key: nat, value: T) modifies this
	
}

class MapStorage<T> extends Storage<T> {

	var storage: map<nat,T>

	constructor() {
		storage := map[];
	}
		
	method get(key: nat) returns (result: Outcome<T>)
	{
		if key in storage {
			result := Success(storage[key]);
		} else {
			result := Failure;
		}
	}

	method put(key: nat, value: T)
		modifies this
	{
		storage := storage[key := value];
	}

}
