

module JavaMocks {

  class Even {

      var value: int;

      function method IsValid() : bool reads this 
      {
          this.value % 2 == 0
      }

      constructor(value: int) 
          requires value % 2 == 0
          ensures this.IsValid()
      {
          this.value := value;
      }

      function method Sum(a: int, b: int) : int 
      {
          a + b
      }
  }
}