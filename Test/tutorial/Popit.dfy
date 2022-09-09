// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// # Pop-it AI solver
///
/// This tutorial covers the following Dafny notions:
/// - Proofs by induction
/// - Mutually recursive predicates (they are not necessary but illustrate interesting points)
/// - Proof of a cache that compute one of the mutually recursive predicates.
/// - Support for arguments in dafny Main functions
/// - Extract the minimum and maximum of a multiset
/// - Invariants for three nested while loops
/// - Reasoning about multisets (sum, induction)
///
/// What is left to the reader:
///
///   Find a simple invariant equivalent to IsWinning, test it with "run" and prove it correct
/// 
/// Usage in development:
/// 
///    > dafny -compile:4 -noVerify Popit.dfy --args play 3 4 5
///    Dafny program verifier did not attempt verification
///    Running...
///    
///    multiset{3, 4, 5} is winning
///    Move to losing state:       
///    Take a sequence of 3 and remove 2 elements to make it a sequence of 1
///
/// Usage in production
///
///    > dafny -compile:2 -noVerify Popit.dfy
///    > dotnet Popit.dll play 3 4 5
///    multiset{3, 4, 5} is winning
///    Move to losing state:       
///    Take a sequence of 3 and remove 2 elements to make it a sequence of 1
///
///    >  dotnet Popit.dll display 4 4
///    Games tested:24
///    multiset{1} is loosing.
///    multiset{1, 1, 1} is loosing.
///    multiset{2, 2} is loosing.
///    multiset{3, 3} is loosing.
///    multiset{4, 4} is loosing.
///    multiset{1, 2, 3} is loosing.

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
/// assert (forall x <- popIt | IsMin(popIt, x), y <- popIt | IsMin(popIt, y) :: x == y);

module {:options "/functionSyntax:4", "/quantifierSyntax:4"} PopItWorld {
  import Printer

/// What is a pop-it game really? Rows with bubbles? 
/// We could encode it in several ways: sequence of sequences of bubbles that are
/// popped or not
/// Or we could just store sequence of sequences of unpopped bubbles.
/// Here we choose the multiset encoding of a PopIt game. This means each
/// number n in the multiset represents a row with a number of n consecutives bubbles.
/// So a PopIt game is a multiset of non-negative integers.
/// Let us define it with a predicate.
/// Since this predicate is never going to be executed, we can mark it as ghost

  ghost predicate IsPopit(x: multiset<int>) {
    forall row <- x :: row > 0
  }

/// Now we define a PopIt as a subset type of a multiset<int> as expected:
/// We decide that the empty multi set is a winning PopIt game,
/// so we don't need to provide a witness since multiset{} is a valid PopIt game

  type PopIt = x: multiset<int> | IsPopit(x)

/// Ok, let's define one useful predicate. A PopIt is said final if it's no longer possible to play

  predicate IsFinal(x: PopIt) {
    |x| == 0
  }

/// The first thing we'll need is a metric to indicate that playing the game will terminate
/// For that, we just sum all the elements of the multiset

  ghost function NumberOfElements(popIt: PopIt): (r: int) ensures (r >= 0)
  {
    if |popIt| == 0 then 0 else
    var x := Pick(popIt);
    x + NumberOfElements(popIt - multiset{x})
  }

/// Picking an element from a set or multiset is easy in ghost mode.
/// We just need to ensure the set or multiset is not empty
/// Indeed, in ghost context, we don't need to prove the uniqueness of the element
/// that we are extracting with `var x :| x in popIt`

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

/// Now, we want to have a say on whether the move is valid for a given PopIt
/// and how to apply it if it is the case.
/// For that, we define a datatype `PopItMove` that will be handy and contain a PopIt game and a move:

  datatype PopItMove = PopItMove(popIt: PopIt, move: Move) {

/// What does it mean for this move to be valid for the PopIt?
/// it means that
/// - that the elements we consider do exist in the original PopIt (`row in popIt`)
/// - that the elements we are removing between index and index+amount are within the range

    predicate Valid() {
        match move {
        case Split(row, index, amount) =>
            row in popIt && 0 <= index < index + amount <= row
        }
    }

/// Now that we defined this notion of move validity,
/// we can define how applying this move results in a new PopIt.
/// Note that, because we defined a datatype, we don't need to repeat the PopIt and move argument
/// This makes signatures smaller and more manageable

    function Apply(): PopIt
      requires Valid()
    {
      match move {
      case Split(row, index, amount) =>

/// In every case, Dafny will verify that we return a valid PopIt, e.g. no element is zero.
/// In the first case, when we remove all the elements of a row, we simply delete it

        if amount == row then
        popIt - multiset{row}

/// In the second case, if we remove elements on either side,
/// it means that we are replacing the row with one smaller row

        else if index == 0 || index + amount == row then
        popIt - multiset{row} + multiset{row-amount}

/// In the third case, if we remove elements from the middle
/// we create two smaller rows

        else
        popIt - multiset{row} + multiset{index} + multiset{row-index-amount}
      }
    }

/// Now we can prove our termination metric. If a move can be applied to a PopIt,
/// we show that its number of elements decreases
/// That way, we can prove that all our recursive functions terminate.

    lemma {:axiom} Decreases()
        requires Valid()
        ensures NumberOfElements(Apply()) < NumberOfElements(popIt)
    {
      match move { 
      case Split(row, index, amount) =>
        if amount == row {

/// We use a Calc statement to compute how the number of bubbles evolves after application,
/// depending on the type of move.
/// "calc" takes expressions and it will try to prove that each expressions equals the next,
/// unless another operator like "<" is provided.
/// We have to use a lemma `NumberOfElementAdditive` that helps us relate the sum of the element of the multiset
/// when adding another element, for both adding and removing elements from the multiset. So:

          calc {
            NumberOfElements(Apply());
            NumberOfElements(popIt - multiset{row});
            { NumberOfElementAdditive(popIt - multiset{row}, row); }
            NumberOfElements(popIt - multiset{row} + multiset{row}) - row;
            { assert popIt == popIt - multiset{row} + multiset{row}; }
            NumberOfElements(popIt) - row;
            < NumberOfElements(popIt);
          }

/// The second and third case are very similar

        } else if index == 0 || index + amount == row {
          calc {
            NumberOfElements(Apply());
            NumberOfElements(popIt - multiset{row} + multiset{row-amount});
            { NumberOfElementAdditive(popIt-multiset{row}, row-amount); }
            NumberOfElements(popIt - multiset{row}) + row - amount;
            { NumberOfElementAdditive(popIt-multiset{row}, row); }
            NumberOfElements(popIt-multiset{row} + multiset{row}) - amount;
            { assert popIt == popIt-multiset{row} + multiset{row}; }
            NumberOfElements(popIt) - amount;
            < NumberOfElements(popIt);
          }
        } else {
          calc {
            NumberOfElements(Apply());
            NumberOfElements(popIt - multiset{row} + multiset{index} + multiset{row-index-amount});
            { NumberOfElementAdditive(popIt - multiset{row} + multiset{index}, row-index-amount);}
            NumberOfElements(popIt - multiset{row} + multiset{index}) + row-index-amount;
            { NumberOfElementAdditive(popIt - multiset{row}, index);}
            NumberOfElements(popIt - multiset{row}) + index + row-index-amount;
            { NumberOfElementAdditive(popIt-multiset{row}, row); }
            NumberOfElements(popIt - multiset{row} + multiset{row}) - row + index + row-index-amount;
            { assert popIt == popIt-multiset{row} + multiset{row}; }
            NumberOfElements(popIt) - row + index + row-index-amount;
            NumberOfElements(popIt) - amount;
            < NumberOfElements(popIt);
          }
        }
      }
    }

/// We can prove interesting small lemmas, such as if this move leads to
/// a losing position, then this popit is winning

    lemma OneMoveLosesImpliesIsWinning()
      requires Valid() && IsLosing(Apply())
      ensures IsWinning(popIt)
    {

    }
  }

/// Now that we know how to verify a move and apply it,
/// we might want to find all the moves that can be applied for a given PopIt game.
/// Here is how we do this, a nested set comprehension with the variables row, index and amount.

  function MovesFor(popIt: PopIt): (result: set<Move>)
  {
    set row <- popIt, index | 0 <= index < row, amount | 1 <= amount <= row - index ::
      Split(row, index, amount)
  }

/// We first prove that all these moves are correct. That is not difficult for Dafny:

  lemma MovesForCorrect(popIt: PopIt)
    ensures forall move <- MovesFor(popIt) :: PopItMove(popIt, move).Valid()
  {
  }

/// The way we defined `MovesFor` makes it also very easy to verify that,
/// if a move is valid, then it has to be in the set returned by `MovesFor`
/// That way, we can prove exhaustivity.
/// Under the hood, set and forall are very similar so that's why it's easy to prove for Dafny

  lemma MovesForExhaustive(popIt: PopIt)
    ensures forall move: Move | PopItMove(popIt, move).Valid() :: move in MovesFor(popIt)
  {
  }

/// To prove that the our metric is additive,
/// we first prove this lemma inspired by http://leino.science/papers/krml274.html

  lemma NumberOfElementSubstractive(s: PopIt, y: int)
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
/// the element has to be in the PöpIt

  lemma NumberOfElementAdditive(popIt: PopIt, row: int)
    requires row > 0
    ensures NumberOfElements(popIt) + row == NumberOfElements(popIt + multiset{row}) {
      NumberOfElementSubstractive(popIt + multiset{row}, row);
    assert popIt + multiset{row} - multiset{row} == popIt;
  }

/// Great! We are almost there. We now need a specification to tell
/// when a pop-it game is winning and when a pop-it game is loosing.
/// We define this status as two mutually recursive predicates.
/// Of course could have defined only one, but it's an interesting exercise
/// to prove that one excludes the other, so let's do it.
/// Although this function is compilable, meaning we can run it directly on at
/// PopIt game to check if it's winning, in practice it's completely suboptimal
/// because it will revisit endgames an exponential number of times

  predicate IsWinning(popIt: PopIt)
    decreases NumberOfElements(popIt)
  {

/// A winning popt it game is either final

    || IsFinal(popIt)

/// Or there exists a move that will enter the game into a losing position
/// Note how we prove termination here by calling the lemma `Decreases`

    || exists 
      row: int <- popIt, index | 0 <= index < row, amount | 1 <= amount <= row - index ::
      var move := Split(row, index, amount);
      IsLosing(PopItMove(popIt, move).Decreases();PopItMove(popIt, move).Apply())
  }

/// Similarly, for a position to be losing

  predicate IsLosing(popIt: PopIt)
    decreases NumberOfElements(popIt)
  {

/// there need to be remaining moves

    && |popIt| > 0

/// And whatever the chosen move, it leads to a winning position

    && forall 
      row: int <- popIt, index | 0 <= index < row, amount | 1 <= amount <= row - index ::
      var move := Split(row, index, amount);
      IsWinning(PopItMove(popIt, move).Decreases();PopItMove(popIt, move).Apply())
  }

/// What if we have a winning position? We can obtain the winning move
/// by running this method. Easy, no?

  method WinningMoveFor(popIt: PopIt) returns (move: Move)
    requires IsWinning(popIt)
    requires !IsFinal(popIt)
    ensures PopItMove(popIt, move).Valid()
    ensures IsLosing(PopItMove(popIt, move).Apply())
  {
    move :| move in MovesFor(popIt) && IsLosing(PopItMove(popIt, move).Decreases();PopItMove(popIt, move).Apply());
  }

/// Great. Now, let's prove that these two predicates always have different truth value.
/// It sees right but still needs a decent proof.
/// For that, we first create a lemma that returns a move that transforms a winning position
/// into a losing one. Yes, lemmas in Dafny can return values, like methods,
/// so they can prove constructively the existence of something.

  lemma IsWinningImpliesOneMovesLoses(popIt: PopIt) returns (move: Move)
    requires |popIt| > 0
    requires IsWinning(popIt)
    ensures PopItMove(popIt, move).Valid() && IsLosing(PopItMove(popIt, move).Apply())
  {
    assert |popIt| > 0;

/// The existence of these three values is guaranteed by the IsWinning() predicate

    var row: int, index: int, amount: int :| row in popIt && 0 <= index < row && 1 <= amount <= row - index
      && var move := Split(row, index, amount); IsLosing(PopItMove(popIt, move).Apply());
    move := Split(row, index, amount);
    assert IsLosing(PopItMove(popIt, move).Apply());
  }

/// Now, we can prove that IsLosing is always of a different boolean value than IsWinning
/// We do this proof by induction, by contradiction if they were equal.

  lemma IsLosingXOrIsWinning(popIt: PopIt)
    decreases NumberOfElements(popIt)
    ensures IsLosing(popIt) != IsWinning(popIt) {
    if IsLosing(popIt) && IsWinning(popIt) {

/// Ok, if it's winning, then here is a move that transforms the popit into a losing position

      var move := IsWinningImpliesOneMovesLoses(popIt);
      var popIt' := PopItMove(popIt, move).Apply();
      assert IsLosing(popIt');

/// But at the same time, the fact that it's losing means that popIt' is winning

      assert IsWinning(popIt');

/// Hence, by applying this lemma recursively, we get IsLosing(popIt') != IsWinning(popIt')
/// which leads to a contradiction.
/// Note that we still need to invoke the metric to ensure the lemma terminates !

      PopItMove(popIt, move).Decreases();
      IsLosingXOrIsWinning(popIt');
      assert false;
    } else if !IsLosing(popIt) && !IsWinning(popIt) {

/// Similarly, if it's not winning, then Dafny figures out that
/// we can define a move that leads to a non-losing state, and a non-winning state.

      var row: int, index: int, amount: int :| (row in popIt && 0 <= index < row && 1 <= amount <= row - index &&
        var move := Split(row, index, amount);
        !IsWinning(PopItMove(popIt, move).Apply()));
      var move := Split(row, index, amount);
      assert !IsLosing(PopItMove(popIt, move).Apply());

/// As before, we apply the lemma recursively, and we can conclude

      PopItMove(popIt, move).Decreases();
      IsLosingXOrIsWinning(PopItMove(popIt, move).Apply());
    }
  }

/// You can guess, WinningMoveFor, IsWinning and IsLosing above are not handy to compute
/// if a PopIt game is winning or losing
/// This is because the number of cases grows exponentially!
/// We can minimize this effect if we cache the result of IsWinning / IsLosing
/// However, we cannot do this using a by method, so we need a class:

  class PopItSimulator {

/// This class contains a cache, which maps PopIt games to their winning state
/// (true == winning, false == losing)

    var cache: map<PopIt, bool>

/// At the same time, for every winning game, we record the move that transforms it
/// to a losing game. That will be useful for the A.I. to indicate what to do,
/// not just decide on whether the game is winnable or not

    var moveToLose: map<PopIt, Move>

/// When we build this class, it's initially empty and Valid().
/// Valid is defined below

    constructor() ensures Valid() {
      this.cache := map[];
      this.moveToLose := map[];
    }


    predicate Valid() reads this`cache, this`moveToLose {

/// For the cache to be valid, it means that every PopIt in it
/// is bound to the same value as computed by IsWinning(row)

      && (forall popIt <- cache ::
          cache[popIt] == IsWinning(popIt))

/// Moreover, every PopIt in moveToLose must be winning, and 
/// the PopIt played after the move must be losing.
/// Indeed, if a PopIt is winning, it's not automatic that playing
/// it will result in a losing state.

      && (forall popIt <- moveToLose ::
          IsWinning(popIt) &&
          var move := moveToLose[popIt];
          PopItMove(popIt, move).Valid() &&
          IsLosing(PopItMove(popIt, move).Apply()))
    }

/// Now is the recursive and cached method that computes the same boolean value as IsWinning
/// Because we modify the cache, to ensure other elements still keep their value,
/// instead of using a forall, we can use `old(cache.Items) <= cache.Items`
/// We use `{:vcs_split_on_every_assert}` so that Dafny can prove each assertion independently
/// otherwise, it would not even manage to do this.
/// We could have used {:split_here} as well, but it's more heuristic.

    method {:vcs_split_on_every_assert} CheckWinning(popIt: PopIt) returns (isWinning: bool)
      decreases NumberOfElements(popIt)
      requires Valid()
      modifies this`cache, this`moveToLose
      ensures old(cache.Items) <= cache.Items
      ensures isWinning == IsWinning(popIt)
      ensures Valid()

/// We ensure that the cache is updated for this game

      ensures popIt in cache && cache[popIt] == IsWinning(popIt)
    {

/// First base case: if the configuration is already in the cache, we return it.

      if popIt in cache {
        isWinning := cache[popIt];

/// Second base case: if the PopIt game is empty; it's winning.

      } else if |popIt| == 0 {
        assert IsWinning(popIt);
        isWinning := true;
        cache := cache[popIt := isWinning];

/// Third case: The general case
/// To iterate over all the consecutive rows of popIt, we get the length of the
/// maximum row, and filter over the possible rows.
      } else {
        var maximum := MaximumOf(popIt);
        var row := 1;

/// We now need a three times nested while loop to iterate
/// over row (the number of consecutive bubbles in our current popit game),
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
          invariant CheckWinningInvariant0(popIt, row)
        {
          if row in popIt {
            var index := 0;
            while index < row
              invariant Valid()
              invariant 0 <= index <= row
              invariant old(cache.Items) <= cache.Items
              invariant CheckWinningInvariant1(popIt, row, index)
            {
              var amount := 1;
              while amount <= row - index
                invariant Valid()
                invariant 1 <= amount <= row - index + 1
                invariant old(cache.Items) <= cache.Items
                invariant CheckWinningInvariant2(popIt, row, index, amount)
              {

/// Now we are in the middle of the three while loops, and we can
/// build a move that is guaranteed to be correct for the given PopIt

                var move := Split(row, index, amount);
                var popitMove := PopItMove(popIt, move);
                assert popitMove.Valid();

/// Because we need to invoke CheckWinning recursively, we invoke our previous
/// lemma to indicate that our metric decreases, so that Dafny is happy with termination.

                popitMove.Decreases();

/// We apply the move on this popIt, which results in popIt'

                var popIt' := popitMove.Apply();
                
/// Using recursivity (and hopefully the cache),
/// we can obtain if this configuration is winning or not.

                var isWinning' := CheckWinning(popIt');

/// If this configuration is losing, great ! This proves that the popit is
/// winning, so we store the move and exit the method.

                if !isWinning' {
                  assert IsWinning(popIt) by {
                    IsLosingXOrIsWinning(popIt');
                    assert IsLosing(popIt');
                    popitMove.OneMoveLosesImpliesIsWinning();
                  }
                  isWinning := true;
                  cache := cache[popIt := isWinning];
                  moveToLose := moveToLose[popIt := move];
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
        assert |popIt| > 0;
        forall row: int <- popIt, index | 0 <= index < row, amount | 1 <= amount <= row - index
          ensures
            (var move := Split(row, index, amount);
            IsWinning(PopItMove(popIt, move).Decreases();PopItMove(popIt, move).Apply()))
        {

        }
        assert IsLosing(popIt);
        isWinning := false;
        cache := cache[popIt := isWinning];
        IsLosingXOrIsWinning(popIt);
        assert isWinning == IsWinning(popIt);
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

    ghost predicate CheckWinningInvariant0(popIt: PopIt, row: int)
      requires |popIt| > 0
      requires row <= MaximumOf(popIt) + 1
      decreases NumberOfElements(popIt)
    {
      forall 
        row0 <- popIt | 0 <= row0 < row, index | 0 <= index < row0, amount | 1 <= amount <= row0 - index ::
        var move := Split(row0, index, amount);
        assert PopItMove(popIt, move).Valid();
        assert NumberOfElements(PopItMove(popIt, move).Apply()) < NumberOfElements(popIt) by {
        PopItMove(popIt, move).Decreases();
        }
        IsWinning(PopItMove(popIt, move).Apply())
    }

    ghost predicate CheckWinningInvariant1(popIt: PopIt, row: int, index: int)
      requires |popIt| > 0
      requires row <= MaximumOf(popIt)
      requires 0 <= index <= row
      decreases NumberOfElements(popIt)
    {
      forall 
          row0 <- popIt | 0 <= row0 <= row,
          index0 | if row != row0 then 0 <= index0 < row0 else 0 <= index0 < index,
          amount | 1 <= amount <= row0 - index0 ::
        var move := Split(row0, index0, amount);
        assert PopItMove(popIt, move).Valid();
        assert NumberOfElements(PopItMove(popIt, move).Apply()) < NumberOfElements(popIt) by {
          PopItMove(popIt, move).Decreases();
        }
        IsWinning(PopItMove(popIt, move).Apply())
    }

    ghost predicate CheckWinningInvariant2(popIt: PopIt, row: int, index: int, amount: int)
      requires |popIt| > 0
      requires row <= MaximumOf(popIt)
      requires 0 <= index <= row
      requires 1 <= amount <= row - index + 1
      decreases NumberOfElements(popIt)
    {
      forall 
          row0 <- popIt | 0 <= row0 <= row,
          index0 | if row != row0 then 0 <= index0 < row0 else 0 <= index0 <= index,
          amount0 | if row != row0 || index0 != index then
            1 <= amount0 <= row0 - index0
            else
            1 <= amount0 < amount::
        var move := Split(row0, index0, amount0);
        assert PopItMove(popIt, move).Valid();
        assert NumberOfElements(PopItMove(popIt, move).Apply()) < NumberOfElements(popIt) by {
        PopItMove(popIt, move).Decreases();
        }
        IsWinning(PopItMove(popIt, move).Apply())
    }
  }

/// Above, we used the compilable function `MaximumOf`. Howevever, finding the maximum of a multiset
/// is not a trivial task.
/// First, we need a lemma that indicates that the <= relation is kept when taking the cardinalities of the multiset:
/// It requires induction to prove.

  lemma MultisetInclusionImpliesSmaller<T>(popIt: multiset<T>, popIt': multiset<T>)
    requires popIt <= popIt'
    ensures |popIt| <= |popIt'|
  {
    if |popIt| == 0 {
    } else {
      var e :| e in popIt;
      MultisetInclusionImpliesSmaller(popIt-multiset{e}, popIt'-multiset{e});
    }
  }

/// Now, we need to prove that the maximum row of a PopIt exists,
/// when this PopIt is not empty

  lemma MaximumExists(popIt: PopIt) returns (row: nat)
    requires |popIt| > 0
    ensures row in popIt && forall row <- popIt :: row <= row;
  {

/// First, we take a random element from popIt

    row :| row in popIt;

/// If there is only one element, we prove that this is the maximum
/// To do so, we do a proof by contradiction. If another element of the set
/// is greater than that one, then there are two elements in the set,
/// which means that 1 == 2, contradiction

    if |popIt| == 1 {
      forall otherRow <-popIt ensures otherRow <= row {
        if otherRow > row {
          MultisetInclusionImpliesSmaller(multiset{otherRow, row}, popIt);
          assert false;
        }
      }
      assert forall otherRow <- popIt :: otherRow <= row;

/// Otherwise, we take the maximum between this element and the
/// remaining multiset

    } else {
      var row' := MaximumExists(popIt - multiset{row});
      if row' > row {
        row := row';
      }
    }
  }

/// Now we are ready to compute the maximum
/// It's a O(n²) algorithm and can be optimized, but for now that's good enough

  function MaximumOf(popIt: PopIt): (r: nat)
    requires |popIt| > 0
    ensures r > 0 && r in popIt && forall row <- popIt :: row <= r
  {
    assert exists r :: r in popIt && forall row <- popIt :: row <= r by {
      var rTmp := MaximumExists(popIt);
    }
    var r :| r in popIt && forall row <- popIt :: row <= r;
    r
  }

/// Time to interface with the command line!
/// We define a way to create all the popit games that have a <size> number of rows
/// each having <maximum> bubbles in it

  function GamesToTest(size: int, maximum: int): (r: set<PopIt>)
    requires size >= 0
  {
    if size == 0 || maximum == 0 then
      {multiset{}}
    else
      set move | 0 <= move <= maximum, g <- GamesToTest(size-1, move) ::
        var x: PopIt := if move == 0 then g else g + multiset{move};
        x
  }

/// Ok, now, what if we have a very quick function that, given a PopIt,
/// would tell us if this position was winning or not? wouldn't be that great?
/// We define a method that will run this hypothesis over a sample of PopIt games
/// and display a counter-example if it finds one

  method Run(size: int, maximum: int, hypothesis: PopIt -> bool)
    requires size >= 0 && maximum >= 1
  {
    var c := new PopItSimulator();
    var games := GamesToTest(size, maximum);
    var i := 0;
    var total := |games|;
    while |games| > 0
    {
      i := i + 1;
      var game :| game in games;
      var w := c.CheckWinning(game);
      if w != hypothesis(game) {
        print "This game is ", if w then "winning" else "losing", " but the hypothesis says otherwise:\n";
        print game, "\n";
        break;
      }
      games := games - {game};
    }
    print "Tested ", i, " games out of ", total;
  }

/// Here is one such conjecture (that is unfortunately wrong)
/// A configuration might be losing if the number of even rows is even and the number of odd rows is odd.
/// After all, 1 and 1 1 1 are losing

  predicate conjectureIsWinning(popIt: PopIt) {
    !(CountIf(popIt, n => n % 2 == 0) % 2 == 0 && CountIf(popIt, n => n % 2 == 1) % 2 == 1)
  }

/// Here is our helper that counts the number of times PopIt rows satisfy a predicate

  function CountIf(popIt: PopIt, f: int -> bool): int
  {
    if |popIt| == 0 then 0 else
    var x := MaximumOf(popIt);
    var n := if f(x) then 1 else 0;
    n + CountIf(popIt - multiset{x}, f)
  }

/// Ok, now we want to have three ways to run this application
/// The first one `Run` was to run an hypothesis for checking if a PopIt is winnable
/// Second, we want to display all the losing positions
/// reachable from playing a game (Display)
/// Third, we want the A.I. to tell us what to play if a position is winnable
/// and to let us know if the position is not winnable (Play)

/// Here is the Display to find all the losing states

  method Display(biggerGame: PopIt)
  {
    var c := new PopItSimulator();
    var winning := c.CheckWinning(biggerGame);
    var cache := c.cache;
    print "Games tested:", |cache|, "\n";
    while |cache| > 0
      decreases |cache|
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

  method Play(test: PopIt) {
    var c := new PopItSimulator();
    var winning := c.CheckWinning(test);
    if winning {
      print test, " is winning\n";
      
      if(!IsFinal(test) && test in c.moveToLose) {
        print "Move to losing state:\n";
        var Split(row, i, a) := c.moveToLose[test];
        if i == 0 || i + a == row {
          print "Take a sequence of ", row, " and remove ", a, " element", if a > 1 then "s" else "", " to make it a sequence of ", row - a; 
        } else {
          print "Take a sequence of ", row, ", split it into ", i, " and ", row - i - a, " elements"; 
        }
      }
    } else {
      print test, " is loosing";
    }
  }

/// That's it ! Now we need to parse a sequence of strings into a PopIt
/// That way, we can parse command-line arguments
/// We return an error if an argument is not a number

  method ParsePopit(popit: seq<string>) returns (popIt: PopIt, error: string)
  {
    popIt := multiset{};
    for row := 0 to |popit|
    {
      if !Printer.isStringNat(popit[row]) {
        error := popit[row] + " is not a valid number";
        return;
      }
      var r: nat := Printer.stringToNat(popit[row]);
      if r == 0 {
        error := "0 is not a valid number for a popit sequence, at index " + Printer.natToString(row + 1);
        return;
      }
      popIt := popIt + multiset{r};
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
    match command {
      case "play" =>
        var popit, error := ParsePopit(arguments);
        if error != "" {
          print error, "\n";
        } else {
          Play(popit);
        }
      case "run" =>
        Run(2, 2, conjectureIsWinning);
      case "display" =>
        var popit, error := ParsePopit(arguments);
        if error != "" {
          print error, "\n";
        } else {
          Display(popit);
        }
      case unknown =>
        print "unknown command: ", unknown, "\nValid commands are run, display or play";
    }
  }
}