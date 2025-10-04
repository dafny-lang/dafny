// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// # Bubbles A.I.
/// 
/// The game we study in this tutorial is often a kid's toy that has 
/// colored rows of bubbles that can be "popped".
/// On the toy, once all bubbles are popped, flipping the toy makes it possible to start again.
/// One way to play a two player game on this toy is to
/// play a variant of the game of Nim:
/// - A player can pop a number of consecutive bubbles from any row
/// - The player who pops the last bubble loses
/// In the sequel, we will refer to "bubbles" to denote a configuration and "bubble row" or "row" for every row of bubbles.
///
/// In this tutorial, we will use Dafny to model a brute force A.I. that can play the game,
/// We will also show how we can test conjectures about whether states are winning or not.
///
/// This tutorial covers the following Dafny notions:
/// - Proofs by induction
/// - Mutually recursive predicates (they are not necessary but illustrate interesting points)
/// - Proof of a cache that computes one of the mutually recursive predicates.
/// - Support for arguments in dafny *Main* functions
/// - Extracting the minimum and maximum of a multiset of integers
/// - Invariants for nested while loops
/// - Reasoning about multisets (sum, induction)
///
/// What is left to the reader:
///
///   Prove a tested conjecture to be true
/// 
/// Usage in development:
/// 
///    > dafny -compile:4 -noVerify Bubbles.dfy --args play 3 4 5
///    Dafny program verifier did not attempt verification
///    Running...
///    
///    multiset{3, 4, 5} is winning
///    Move to losing state:       
///    Take a sequence of 3 and pop 2 elements to make it a sequence of 1
///
/// Usage in production
///
///    > dafny -compile:2 -noVerify Bubbles.dfy
///    > dotnet Bubbles.dll play 3 4 5
///    multiset{3, 4, 5} is winning
///    Move to losing state:       
///    Take a sequence of 3 and pop 2 elements to make it a sequence of 1
///
///    >  dotnet Bubbles.dll display 4 4
///    Games tested:24
///    multiset{1} is loosing.
///    multiset{1, 1, 1} is loosing.
///    multiset{2, 2} is loosing.
///    multiset{3, 3} is loosing.
///    multiset{4, 4} is loosing.
///    multiset{1, 2, 3} is loosing.
///
///    >  dotnet Bubbles.dll run 6 6
///    Games to test:75
///    Nothing could disprove this conjecture on these 75 games
///

/// First, we need to define a way to convert numbers to strings and vice-versa.
/// This will be useful for parsing arguments
/// We use a variation of https://stackoverflow.com/a/73626804/1287856

module {:options "/functionSyntax:4"} Printer {

/// First, we want to generate meaningful error messages
/// Hence, we need a predicate to check if a string is a valid natural number
/// A valid string-encoded nat must contain only digit and start with '0' only if it's 0 itself

  predicate isStringNat(s: string) {
    |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
    forall i | 0 <= i < |s| :: s[i] in "0123456789"
  }

/// Now we can define a subset type of strings to define valid string-encoded natural numbers
/// We need to give it a witness because the empty string is not a valid natural number

  type stringNat = s: string | isStringNat(s)
    witness "1"

/// We write the first function to convert a number to a string
/// It is straightforward. Note the use of the match without braces
/// This enhance readability

  function natToString(n: nat): stringNat {
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
  }

/// We write the second function to convert a string-encoded natural number to a nat
/// Note the following interesting thing: We recurse on the |s|-1 initial elements of the strings,
/// Recursing that way makes proof to be straightforward for Dafny.
/// The alternative would have been an auxiliary function to accumulate intermediate results,
/// but the proofs become complicated if not unfeasible

  function stringToNat(s: stringNat): nat
    decreases |s|
  {
    if |s| == 1 then
      match s[0]
      case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
      case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
    else
      stringToNat(s[..|s|-1])*10 + stringToNat(s[|s|-1..|s|])
  }

/// Our functions are so well defined that Dafny is able to automatically prove
/// the two equivalence lemmas

  lemma natToStringThenStringToNatIdem(n: nat)
    ensures stringToNat(natToString(n)) == n
  { // Proof is automatic
  }
  lemma stringToNatThenNatToStringIdem(s: stringNat)
    ensures natToString(stringToNat(s)) == s
  { // Proof is automatic
  }
}

/// Ok, now let's move to the really interesting part
/// We wrap everything in a module to be able to use the new function syntax
/// That way, "function" and "predicate" are compilable by default
/// We also use the new quantifier syntax so that the following expression
/// does not result in a parser error. Otherwise, it would try to interpret this as a tuple and would fail.
/// assert (forall x <- bubbles | IsMin(bubbles, x), y <- bubbles | IsMin(bubbles, y) :: x == y);

module {:options "/functionSyntax:4", "/quantifierSyntax:4"} BubblesWorld {
  import Printer

/// What is a pop-it game really? Rows with bubbles? 
/// We could encode it in several ways: sequence of sequences of bubbles that are
/// popped or not
/// Or we could just store sequence of sequences of unpopped bubbles.
/// Here we choose the multiset encoding of a Bubbles game. This means each
/// number n in the multiset represents a row with a number of n consecutives bubbles.
/// So a Bubbles game is a multiset of non-negative integers.
/// Let us define it with a predicate.
/// Since this predicate is never going to be executed, we can mark it as ghost

  ghost predicate IsBubbles(x: multiset<int>) {
    forall row <- x :: row > 0
  }

/// Now we define a Bubbles as a subset type of a multiset<int> as expected:
/// We decide that the empty multi set is a winning Bubbles game,
/// so we don't need to provide a witness since multiset{} is a valid Bubbles game

  type Bubbles = x: multiset<int> | IsBubbles(x)

/// Ok, let's define one useful predicate. A Bubbles is said final if it's no longer possible to play

  predicate IsFinal(x: Bubbles) {
    |x| == 0
  }

/// The first thing we'll need is a metric to indicate that playing the game will terminate
/// For that, we just sum all the elements of the multiset

  ghost function NumberOfElements(bubbles: Bubbles): (r: int) ensures (r >= 0)
  {
    if |bubbles| == 0 then 0 else
    var x := Pick(bubbles);
    x + NumberOfElements(bubbles - multiset{x})
  }

/// Picking an element from a set or multiset is easy in ghost mode.
/// We just need to ensure the set or multiset is not empty
/// Indeed, in ghost context, we don't need to prove the uniqueness of the element
/// that we are extracting with `var x :| x in bubbles`

  ghost function Pick<T>(move: multiset<T>): T
    requires |move| != 0
  {
    var x :| x in move;
    x
  }

/// Now, let's consider the moves. A move consists of considering a number of 'row' consecutive bubbles,
/// and splitting it in two rows of index and row-amount-index rows

  datatype Move =
    Split(row: int, index: int, amount: int)

/// Now, we want to have a say on whether the move is valid for a given Bubbles
/// and how to apply it if it is the case.
/// For that, we define a datatype `BubblesMove` that will be handy and contain a Bubbles game and a move:

  datatype BubblesMove = BubblesMove(bubbles: Bubbles, move: Move) {

/// What does it mean for this move to be valid for the Bubbles?
/// it means that
/// - The elements we consider do exist in the original Bubbles (`row in bubbles`)
/// - The elements we are removing between `index` and `index+amount` are within the range

    predicate Valid() {
        match move
        case Split(row, index, amount) =>
          row in bubbles && 0 <= index < index + amount <= row
    }

/// Now that we defined this notion of move validity,
/// we can define how applying this move results in a new Bubbles.
/// Note that, because we defined a datatype, we don't need to repeat the Bubbles and move argument
/// This makes signatures smaller and more manageable

    function Apply(): Bubbles
      requires Valid()
    {
      match move
      case Split(row, index, amount) =>

/// In every case, Dafny will verify that we return a valid Bubbles, e.g. no row contains zero bubbles.
/// In the first case, when we pop all the elements of a row, we simply delete it

        if amount == row then
        bubbles - multiset{row}

/// In the second case, if we pop elements on either side,
/// it means that we are replacing the row with one smaller row

        else if index == 0 || index + amount == row then
        bubbles - multiset{row} + multiset{row-amount}

/// In the third case, if we pop elements from the middle
/// we create two smaller rows

        else
        bubbles - multiset{row} + multiset{index} + multiset{row-index-amount}
    }

/// Now we can prove our termination metric. If a move can be applied to a Bubbles,
/// we show that its number of elements decreases
/// That way, we can prove that all our recursive functions terminate.

    lemma Decreases()
        requires Valid()
        ensures NumberOfElements(Apply()) < NumberOfElements(bubbles)
    {
      match move
      case Split(row, index, amount) =>
        if amount == row {

/// We use a `calc` statement to compute how the number of bubbles evolves after application,
/// depending on the type of move.
/// `calc` takes expressions and it will try to prove that each expressions equals the next,
/// unless another operator like `<` is provided.
/// We have to use a lemma `NumberOfElementAdditive` that helps us relate the sum of the element of the multiset
/// when adding another element, for both adding and removing elements from the multiset. So:

          calc {
            NumberOfElements(Apply());
            NumberOfElements(bubbles - multiset{row});
            { NumberOfElementAdditive(bubbles - multiset{row}, row); }
            NumberOfElements(bubbles - multiset{row} + multiset{row}) - row;
            { assert bubbles == bubbles - multiset{row} + multiset{row}; }
            NumberOfElements(bubbles) - row;
            < NumberOfElements(bubbles);
          }

/// The second and third case are very similar

        } else if index == 0 || index + amount == row {
          calc {
            NumberOfElements(Apply());
            NumberOfElements(bubbles - multiset{row} + multiset{row-amount});
            { NumberOfElementAdditive(bubbles-multiset{row}, row-amount); }
            NumberOfElements(bubbles - multiset{row}) + row - amount;
            { NumberOfElementAdditive(bubbles-multiset{row}, row); }
            NumberOfElements(bubbles-multiset{row} + multiset{row}) - amount;
            { assert bubbles == bubbles-multiset{row} + multiset{row}; }
            NumberOfElements(bubbles) - amount;
            < NumberOfElements(bubbles);
          }
        } else {
          calc {
            NumberOfElements(Apply());
            NumberOfElements(bubbles - multiset{row} + multiset{index} + multiset{row-index-amount});
            { NumberOfElementAdditive(bubbles - multiset{row} + multiset{index}, row-index-amount);}
            NumberOfElements(bubbles - multiset{row} + multiset{index}) + row-index-amount;
            { NumberOfElementAdditive(bubbles - multiset{row}, index);}
            NumberOfElements(bubbles - multiset{row}) + index + row-index-amount;
            { NumberOfElementAdditive(bubbles-multiset{row}, row); }
            NumberOfElements(bubbles - multiset{row} + multiset{row}) - row + index + row-index-amount;
            { assert bubbles == bubbles-multiset{row} + multiset{row}; }
            NumberOfElements(bubbles) - row + index + row-index-amount;
            NumberOfElements(bubbles) - amount;
            < NumberOfElements(bubbles);
          }
      }
    }

/// We can prove interesting small lemmas, such as if this move leads to
/// a losing position, then this bubbles is winning

    lemma OneMoveLosesImpliesIsWinning()
      requires Valid() && IsLosing(Apply())
      ensures IsWinning(bubbles)
    {

    }
  }

/// Now that we know how to verify a move and apply it,
/// we might want to find all the moves that can be applied for a given Bubbles game.
/// Here is how we do this, a nested set comprehension with the variables row, index and amount.

  function MovesFor(bubbles: Bubbles): (result: set<Move>)
  {
    set row <- bubbles, index | 0 <= index < row, amount | 1 <= amount <= row - index ::
      Split(row, index, amount)
  }

/// We first prove that all these moves are correct. That is not difficult for Dafny:

  lemma MovesForCorrect(bubbles: Bubbles)
    ensures forall move <- MovesFor(bubbles) :: BubblesMove(bubbles, move).Valid()
  {
  }

/// The way we defined `MovesFor` makes it also very easy to verify that,
/// if a move is valid, then it has to be in the set returned by `MovesFor`
/// That way, we can prove exhaustivity.
/// Under the hood, set and forall are very similar so that's why it's easy to prove for Dafny

  lemma MovesForExhaustive(bubbles: Bubbles)
    ensures forall move: Move | BubblesMove(bubbles, move).Valid() :: move in MovesFor(bubbles)
  {
  }

/// To prove that the our metric is additive,
/// we first prove this lemma inspired by http://leino.science/papers/krml274.html

  lemma NumberOfElementSubstractive(s: Bubbles, y: int)
    requires y in s
    ensures NumberOfElements(s) == y + NumberOfElements(s - multiset{y})
  {
    var x := Pick(s);
    if y == x {
    } else {
      calc {
        NumberOfElements(s);
      ==  // def. Sum
        x + NumberOfElements(s - multiset{x});
      ==  { NumberOfElementSubstractive(s - multiset{x}, y); }
        x + y + NumberOfElements(s - multiset{x} - multiset{y});
      ==  { assert s - multiset{x} - multiset{y} == s - multiset{y} - multiset{x}; }
        y + x + NumberOfElements(s - multiset{y} - multiset{x});
      ==  { NumberOfElementSubstractive(s - multiset{y}, x); }
        y + NumberOfElements(s - multiset{y});
      }
    }
  }

/// Now we prove the lemma about the additivity of counting the bubbles,
/// as we used it earlier. That way, we can get rid of the precondition that
/// the element has to be in the Bubbles.

  lemma NumberOfElementAdditive(bubbles: Bubbles, row: int)
    requires row > 0
    ensures NumberOfElements(bubbles) + row == NumberOfElements(bubbles + multiset{row}) {
      NumberOfElementSubstractive(bubbles + multiset{row}, row);
    assert bubbles + multiset{row} - multiset{row} == bubbles;
  }

/// Great! We are almost there. We now need a specification to tell
/// when a pop-it game is winning and when a pop-it game is loosing.
/// We define this status as two mutually recursive predicates.
/// Of course could have defined only one, but it's an interesting exercise
/// to prove that one excludes the other, so let's do it.
/// Although this function is compilable, meaning we can run it directly on at
/// Bubbles game to check if it's winning, in practice it's completely suboptimal
/// because it will revisit endgames an exponential number of times

  predicate IsWinning(bubbles: Bubbles)
    decreases NumberOfElements(bubbles)
  {

/// A winning popt it game is either final

    || IsFinal(bubbles)

/// Or there exists a move that will enter the game into a losing position
/// Note how we prove termination here by calling the lemma `Decreases`

    || exists 
       row: int <- bubbles, index | 0 <= index < row, amount | 1 <= amount <= row - index ::
       var move := Split(row, index, amount);
       IsLosing(BubblesMove(bubbles, move).Decreases();BubblesMove(bubbles, move).Apply())
  }

/// Similarly, for a position to be losing

  predicate IsLosing(bubbles: Bubbles)
    decreases NumberOfElements(bubbles)
  {

/// there need to be remaining moves

    && |bubbles| > 0

/// And whatever the chosen move, it leads to a winning position

    && forall 
      row: int <- bubbles, index | 0 <= index < row, amount | 1 <= amount <= row - index ::
      var move := Split(row, index, amount);
      IsWinning(BubblesMove(bubbles, move).Decreases();BubblesMove(bubbles, move).Apply())
  }

/// What if we have a winning position? We can obtain the winning move
/// by running this method. Easy, no?

  method WinningMoveFor(bubbles: Bubbles) returns (move: Move)
    requires IsWinning(bubbles)
    requires !IsFinal(bubbles)
    ensures BubblesMove(bubbles, move).Valid()
    ensures IsLosing(BubblesMove(bubbles, move).Apply())
  {
    move :| move in MovesFor(bubbles) && IsLosing(BubblesMove(bubbles, move).Decreases();BubblesMove(bubbles, move).Apply());
  }

/// Great. Now, let's prove that these two predicates always have different truth value.
/// It sees right but still needs a decent proof.
/// For that, we first create a lemma that returns a move that transforms a winning position
/// into a losing one. Yes, lemmas in Dafny can return values, like methods,
/// so they can prove constructively the existence of something.

  lemma IsWinningImpliesOneMovesLoses(bubbles: Bubbles) returns (move: Move)
    requires |bubbles| > 0
    requires IsWinning(bubbles)
    ensures BubblesMove(bubbles, move).Valid() && IsLosing(BubblesMove(bubbles, move).Apply())
  {
    assert |bubbles| > 0;

/// The existence of these three values is guaranteed by the IsWinning() predicate

    var row: int, index: int, amount: int :| row in bubbles && 0 <= index < row && 1 <= amount <= row - index
      && var move := Split(row, index, amount); IsLosing(BubblesMove(bubbles, move).Apply());
    move := Split(row, index, amount);
    assert IsLosing(BubblesMove(bubbles, move).Apply());
  }

/// Now, we can prove that IsLosing is always of a different boolean value than IsWinning
/// We do this proof by induction, by contradiction if they were equal.

  lemma IsLosingXOrIsWinning(bubbles: Bubbles)
    decreases NumberOfElements(bubbles)
    ensures IsLosing(bubbles) != IsWinning(bubbles) {
    if IsLosing(bubbles) && IsWinning(bubbles) {

/// Ok, if it's winning, then here is a move that transforms the bubbles into a losing position

      var move := IsWinningImpliesOneMovesLoses(bubbles);
      var bubbles' := BubblesMove(bubbles, move).Apply();
      assert IsLosing(bubbles');

/// But at the same time, the fact that it's losing means that bubbles' is winning

      assert IsWinning(bubbles');

/// Hence, by applying this lemma recursively, we get IsLosing(bubbles') != IsWinning(bubbles')
/// which leads to a contradiction.
/// Note that we still need to invoke the metric to ensure the lemma terminates !

      BubblesMove(bubbles, move).Decreases();
      IsLosingXOrIsWinning(bubbles');
      assert false;
    } else if !IsLosing(bubbles) && !IsWinning(bubbles) {

/// Similarly, if it's not winning, then Dafny figures out that
/// we can define a move that leads to a non-losing state, and a non-winning state.

      var row: int, index: int, amount: int :| (row in bubbles && 0 <= index < row && 1 <= amount <= row - index &&
        var move := Split(row, index, amount);
        !IsWinning(BubblesMove(bubbles, move).Apply()));
      var move := Split(row, index, amount);
      assert !IsLosing(BubblesMove(bubbles, move).Apply());

/// As before, we apply the lemma recursively, and we can conclude

      BubblesMove(bubbles, move).Decreases();
      IsLosingXOrIsWinning(BubblesMove(bubbles, move).Apply());
    }
  }

/// You can guess, WinningMoveFor, IsWinning and IsLosing above are not handy to compute
/// if a Bubbles game is winning or losing
/// This is because the number of cases grows exponentially!
/// We can minimize this effect if we cache the result of IsWinning / IsLosing
/// However, we cannot do this using a by method, so we need a class:

  class BubblesSimulator {

/// This class contains a cache, which maps Bubbles games to their winning state
/// (true == winning, false == losing)

    var cache: map<Bubbles, bool>

/// At the same time, for every winning game, we record the move that transforms it
/// to a losing game. That will be useful for the A.I. to indicate what to do,
/// not just decide on whether the game is winnable or not

    var moveToLose: map<Bubbles, Move>

/// When we build this class, it's initially empty and Valid().
/// Valid is defined below

    constructor() ensures Valid() {
      this.cache := map[];
      this.moveToLose := map[];
    }


    predicate Valid() reads this`cache, this`moveToLose {

/// For the cache to be valid, it means that every Bubbles in it
/// is bound to the same value as computed by IsWinning(row)

      && (forall bubbles <- cache ::
          cache[bubbles] == IsWinning(bubbles))

/// Moreover, every Bubbles in moveToLose must be winning, and 
/// the Bubbles played after the move must be losing.
/// Indeed, if a Bubbles is winning, it's not automatic that playing
/// it will result in a losing state.

      && (forall bubbles <- moveToLose ::
          IsWinning(bubbles) &&
          var move := moveToLose[bubbles];
          BubblesMove(bubbles, move).Valid() &&
          IsLosing(BubblesMove(bubbles, move).Apply()))
    }

/// Now is the recursive and cached method that computes the same boolean value as IsWinning
/// Because we modify the cache, to ensure other elements still keep their value,
/// instead of using a forall, we can use `old(cache.Items) <= cache.Items`
/// We use `{:vcs_split_on_every_assert}` so that Dafny can prove each assertion independently
/// otherwise, it would not even manage to do this.
/// We could have used {:split_here} as well, but it's more heuristic.

    method {:vcs_split_on_every_assert} CheckWinning(bubbles: Bubbles) returns (isWinning: bool)
      decreases NumberOfElements(bubbles)
      requires Valid()
      modifies this`cache, this`moveToLose
      ensures old(cache.Items) <= cache.Items
      ensures isWinning == IsWinning(bubbles)
      ensures Valid()

/// We ensure that the cache is updated for this game

      ensures bubbles in cache && cache[bubbles] == IsWinning(bubbles)
    {

/// First base case: if the configuration is already in the cache, we return it.

      if bubbles in cache {
        isWinning := cache[bubbles];

/// Second base case: if the Bubbles game is empty; it's winning.

      } else if |bubbles| == 0 {
        assert IsWinning(bubbles);
        isWinning := true;
        cache := cache[bubbles := isWinning];

/// Third case: The general case
/// To iterate over all the consecutive rows of bubbles, we get the length of the
/// maximum row, and filter over the possible rows.
      } else {
        var maximum := MaximumOf(bubbles);
        var row := 1;

/// We now need a three times nested while loop to iterate
/// over row (the number of consecutive bubbles in our current bubbles game),
/// index (where we start popping bubbles),
/// and amount (how many consecutive bubbles we pop)
/// What this loop does is looking for a move that, if applied, results in a
/// loosing position.
/// Hence, the invariant we have in the outer loop is an inductive invariant
/// that will prove IsLosing() if it exit properly, since IsLosing is a forall statement,
/// and finishing the loop means that we haven't find a move that results in
/// losing position.

        while row <= maximum

/// Because row will be equal to maximum + 1 on the last round the decreases expression must be non-negative,
/// so we end up with this expression

          decreases (maximum+1) - row
          invariant Valid()
          invariant row <= maximum + 1
          invariant old(cache.Items) <= cache.Items
          invariant CheckWinningInvariant0(bubbles, row)
        {
          if row in bubbles {
            var index := 0;
            while index < row
              invariant Valid()
              invariant 0 <= index <= row
              invariant old(cache.Items) <= cache.Items
              invariant CheckWinningInvariant1(bubbles, row, index)
            {
              var amount := 1;
              while amount <= row - index
                invariant Valid()
                invariant 1 <= amount <= row - index + 1
                invariant old(cache.Items) <= cache.Items
                invariant CheckWinningInvariant2(bubbles, row, index, amount)
              {

/// Now we are in the middle of the three while loops, and we can
/// build a move that is guaranteed to be correct for the given Bubbles

                var move := Split(row, index, amount);
                var bubblesMove := BubblesMove(bubbles, move);
                assert bubblesMove.Valid();

/// Because we need to invoke CheckWinning recursively, we invoke our previous
/// lemma to indicate that our metric decreases, so that Dafny is happy with termination.

                bubblesMove.Decreases();

/// We apply the move on this bubbles, which results in bubbles'

                var bubbles' := bubblesMove.Apply();
                
/// Using recursivity (and hopefully the cache),
/// we can obtain if this configuration is winning or not.

                var isWinning' := CheckWinning(bubbles');

/// If this configuration is losing, great ! This proves that the bubbles is
/// winning, so we store the move and exit the method.

                if !isWinning' {
                  assert IsWinning(bubbles) by {
                    IsLosingXOrIsWinning(bubbles');
                    assert IsLosing(bubbles');
                    bubblesMove.OneMoveLosesImpliesIsWinning();
                  }
                  isWinning := true;
                  cache := cache[bubbles := isWinning];
                  moveToLose := moveToLose[bubbles := move];
                  return;
                }
                amount := amount + 1;
              }
              index := index + 1;
            }
          }
          row := row + 1;
        }

/// Now that we explored all the paths, the invariants state basically that
/// every move leads to a winning position. So it's a losing position
/// and we can prove it.

        assert row == maximum + 1;
        assert |bubbles| > 0;
        forall row: int <- bubbles, index | 0 <= index < row, amount | 1 <= amount <= row - index
          ensures
            (var move := Split(row, index, amount);
            IsWinning(BubblesMove(bubbles, move).Decreases();BubblesMove(bubbles, move).Apply()))
        {

        }
        assert IsLosing(bubbles);
        isWinning := false;
        cache := cache[bubbles := isWinning];
        IsLosingXOrIsWinning(bubbles);
        assert isWinning == IsWinning(bubbles);
      }
    }

/// The three invariants have the same shape, but notice the differences.
/// These differences makes it possible to prove every outer invariant based on the inner one
/// - `CheckWinningInvariant0` iterates row0 between 0 and row (excluded)
/// - `CheckWinningInvariant1` iterates row0 between 0 and row (included!),
///   and iterates index0 between 0 and row0 (excluded) if row0 is was a previous row,
///   otherwise it iterates until the provided index (excluded)
/// - `CheckWinningInvariant2` iterates row0 between 0 and row (included!),
///   and iterates index0 between 0 and row0 (excluded) if row0 is was a previous row,
///   otherwise it iterates until the provided index (included!)
///   and iterates amount0 between 1 and row0 - index0 if index0 is not the current index,
///   otherwise between 1 and index (excluded)

    ghost predicate CheckWinningInvariant0(bubbles: Bubbles, row: int)
      requires |bubbles| > 0
      requires row <= MaximumOf(bubbles) + 1
      decreases NumberOfElements(bubbles)
    {
      forall 
        row0 <- bubbles | 0 <= row0 < row, index | 0 <= index < row0, amount | 1 <= amount <= row0 - index ::
        var move := Split(row0, index, amount);
        assert BubblesMove(bubbles, move).Valid();
        assert NumberOfElements(BubblesMove(bubbles, move).Apply()) < NumberOfElements(bubbles) by {
        BubblesMove(bubbles, move).Decreases();
        }
        IsWinning(BubblesMove(bubbles, move).Apply())
    }

    ghost predicate CheckWinningInvariant1(bubbles: Bubbles, row: int, index: int)
      requires |bubbles| > 0
      requires row <= MaximumOf(bubbles)
      requires 0 <= index <= row
      decreases NumberOfElements(bubbles)
    {
      forall 
          row0 <- bubbles | 0 <= row0 <= row,
          index0 | if row != row0 then 0 <= index0 < row0 else 0 <= index0 < index,
          amount | 1 <= amount <= row0 - index0 ::
        var move := Split(row0, index0, amount);
        assert BubblesMove(bubbles, move).Valid();
        assert NumberOfElements(BubblesMove(bubbles, move).Apply()) < NumberOfElements(bubbles) by {
          BubblesMove(bubbles, move).Decreases();
        }
        IsWinning(BubblesMove(bubbles, move).Apply())
    }

    ghost predicate CheckWinningInvariant2(bubbles: Bubbles, row: int, index: int, amount: int)
      requires |bubbles| > 0
      requires row <= MaximumOf(bubbles)
      requires 0 <= index <= row
      requires 1 <= amount <= row - index + 1
      decreases NumberOfElements(bubbles)
    {
      forall 
          row0 <- bubbles | 0 <= row0 <= row,
          index0 | if row != row0 then 0 <= index0 < row0 else 0 <= index0 <= index,
          amount0 | if row != row0 || index0 != index then
            1 <= amount0 <= row0 - index0
            else
            1 <= amount0 < amount::
        var move := Split(row0, index0, amount0);
        assert BubblesMove(bubbles, move).Valid();
        assert NumberOfElements(BubblesMove(bubbles, move).Apply()) < NumberOfElements(bubbles) by {
        BubblesMove(bubbles, move).Decreases();
        }
        IsWinning(BubblesMove(bubbles, move).Apply())
    }
  }

/// Above, we used the compilable function `MaximumOf`. Howevever, finding the maximum of a multiset
/// is not a trivial task.
/// First, we need a lemma that indicates that the <= relation is kept when taking the cardinalities of the multiset:
/// It requires induction to prove.

  lemma MultisetInclusionImpliesSmaller<T>(bubbles: multiset<T>, bubbles': multiset<T>)
    requires bubbles <= bubbles'
    ensures |bubbles| <= |bubbles'|
  {
    if |bubbles| == 0 {
    } else {
      var e :| e in bubbles;
      MultisetInclusionImpliesSmaller(bubbles-multiset{e}, bubbles'-multiset{e});
    }
  }

/// Now, we need to prove that the maximum row of a Bubbles exists,
/// when this Bubbles is not empty

  lemma MaximumExists(bubbles: Bubbles) returns (row: nat)
    requires |bubbles| > 0
    ensures row in bubbles && forall r <- bubbles :: r <= row;
  {

/// First, we take a random element from bubbles

    row :| row in bubbles;

/// If there is only one element, we prove that this is the maximum
/// To do so, we do a proof by contradiction. If another element of the set
/// is greater than that one, then there are two elements in the set,
/// which means that 1 == 2, contradiction

    if |bubbles| == 1 {
      forall otherRow <-bubbles ensures otherRow <= row {
        if otherRow > row {
          MultisetInclusionImpliesSmaller(multiset{otherRow, row}, bubbles);
          assert false;
        }
      }
      assert forall otherRow <- bubbles :: otherRow <= row;

/// Otherwise, we take the maximum between this element and the
/// remaining multiset

    } else {
      var row' := MaximumExists(bubbles - multiset{row});
      if row' > row {
        row := row';
      }
    }
  }

/// Now we are ready to compute the maximum
/// It's a O(n²) algorithm and can be optimized, but for now that's good enough

  function MaximumOf(bubbles: Bubbles): (r: nat)
    requires |bubbles| > 0
    ensures r > 0 && r in bubbles && forall row <- bubbles :: row <= r
  {
    assert exists r <- bubbles :: forall row <- bubbles :: row <= r by {
      var rTmp := MaximumExists(bubbles);
    }
    var r :| r in bubbles && forall row <- bubbles :: row <= r;
    r
  }

/// Time to interface with the command line!
/// We define a way to create all the bubbles games that have a <size> number of rows
/// each having <maximum> bubbles in it

  function GamesToTest(size: int, maximum: int): (r: set<Bubbles>)
    requires size >= 0
  {
    if size == 0 || maximum == 0 then
      {multiset{}}
    else
      set move | 0 <= move <= maximum, g <- GamesToTest(size-1, move) ::
        var x: Bubbles := if move == 0 then g else g + multiset{move};
        x
  }

/// Ok, now, what if we have a very quick function that, given a Bubbles,
/// would tell us if this position was winning or not? wouldn't be that great?
/// We define a method that will run this hypothesis over a sample of Bubbles games
/// and display a counter-example if it finds one

  method Run(bubbles: Bubbles, hypothesis: Bubbles -> bool)
  {
    var c := new BubblesSimulator();
    var winning := c.CheckWinning(bubbles);
    var cache := c.cache;
    var i := 0;
    print "Games to test:", |cache|, "\n";
    while |cache.Keys| > 0
      decreases |cache.Keys|
    {
      i := i + 1;
      var game :| game in cache;
      var w := cache[game];
      if  w  != hypothesis(game) {
        print "This game is ", if w then "winning" else "losing", " but the hypothesis says otherwise:\n";
        print game, "\n";
        print "It was the game number ", i, ".";
        return;
      }
      cache := cache - {game};
    }
    
    print "Nothing could disprove this conjecture on these ", i, " games";
  }
/// Here is one such conjecture (that is is probably correct)
/// Exercise left to the reader: Prove this conjecture

  predicate conjectureIsWinning(bubbles: Bubbles) {
    if forall i <- bubbles :: i == 1 then |bubbles| % 2 == 0
    else Reduce(bubbles, 0, xor) != 0
  }

  function {:tailrecursion false} xor(a: nat, b: nat): nat
    decreases a
  {
    if a == 0 then b else if b == 0 then a
    else if a%2 == b%2 then xor(a/2, b/2)*2 else xor(a/2, b/2)*2 + 1
  }

  function Reduce<T>(bubbles: Bubbles, acc: T, f: (nat, T) -> T): T
  {
    if |bubbles| == 0 then acc else
    var x := MaximumOf(bubbles);
    Reduce(bubbles-multiset{x}, f(x,acc), f)
  }

/// Here is our helper that counts the number of times Bubbles rows satisfy a predicate

  function CountIf(bubbles: Bubbles, f: int -> bool): int
  {
    if |bubbles| == 0 then 0 else
    var x := MaximumOf(bubbles);
    var n := if f(x) then 1 else 0;
    n + CountIf(bubbles - multiset{x}, f)
  }

/// Ok, now we want to have three ways to run this application
/// The first one `Run` was to run an hypothesis for checking if a Bubbles is winnable
/// Second, we want to display all the losing positions
/// reachable from playing a game (Display)
/// Third, we want the A.I. to tell us what to play if a position is winnable
/// and to let us know if the position is not winnable (Play)

/// Here is the Display to find all the losing states

  method Display(biggerGame: Bubbles)
  {
    var c := new BubblesSimulator();
    var winning := c.CheckWinning(biggerGame);
    var cache := c.cache;
    print "Games tested:", |cache|, "\n";
    while |cache.Keys| > 0
      decreases |cache.Keys|
    {
      var game :| game in cache;
      if !cache[game] {
        print game, " is loosing.\n";
      }
      cache := cache - {game};
    }
  }

/// Here is our A.I. to play the game
/// and show us a winning move iff it exists

  method Play(test: Bubbles) {
    var c := new BubblesSimulator();
    var winning := c.CheckWinning(test);
    if winning {
      print test, " is winning\n";
      
      if(!IsFinal(test) && test in c.moveToLose) {
        print "Move to losing state:\n";
        var Split(row, i, a) := c.moveToLose[test];
        if i == 0 || i + a == row {
          print "Take a sequence of ", row, " and pop ", a, " bubble", if a > 1 then "s" else "", " to make it a sequence of ", row - a; 
        } else {
          print "Take a sequence of ", row, ", split it into ", i, " and ", row - i - a, " elements"; 
        }
      }
    } else {
      print test, " is loosing";
    }
  }

/// That's it ! Now we need to parse a sequence of strings into a Bubbles
/// That way, we can parse command-line arguments
/// We return an error if an argument is not a number

  method ParseBubbles(bubblesSeq: seq<string>) returns (bubbles: Bubbles, error: string)
  {
    bubbles := multiset{};
    for row := 0 to |bubblesSeq|
    {
      if !Printer.isStringNat(bubblesSeq[row]) {
        error := bubblesSeq[row] + " is not a valid number";
        return;
      }
      var r: nat := Printer.stringToNat(bubblesSeq[row]);
      if r == 0 {
        error := "0 is not a valid number for a bubbles sequence, at index " + Printer.natToString(row + 1);
        return;
      }
      bubbles := bubbles + multiset{r};
    }
  }

/// Finally, we can define our main function,
/// that will take care of dispatching the arguments to the correct
/// location

  method Main(args: seq<string>) {
    if |args| <= 1 {
      print "Provide at least one command: run, display or play";
      return;
    }
    var command := args[1];
    var arguments := args[2..];
    var bubbles, error := ParseBubbles(arguments);
    if error != "" {
      print error, "\n";
    } else {
      match command {
        case "play" =>
          Play(bubbles);
        case "run" =>
          Run(bubbles, conjectureIsWinning);
        case "display" =>
          Display(bubbles);
        case unknown =>
          print "unknown command: ", unknown, "\nValid commands are run, display or play";
      }
    }
  }
}