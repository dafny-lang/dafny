"""Tests for _dafny.tuple_eq, the comparator the Python backend emits for a tuple
that holds a reference.

A Dafny tuple compiles to a native Python tuple, whose __eq__ compares components
with ==. That is wrong for a component of a reference type, whose Dafny equality is
identity, and a native tuple cannot be given a custom __eq__. So the compiler emits
tuple_eq with a mask saying which components are references.
"""

import unittest

import _dafny


class Overriding:
    """Stands for an extern class that defines its own equality, as the extern in
    dafny-lang/dafny#6491 does."""

    def __eq__(self, other):
        return isinstance(other, Overriding)

    def __hash__(self):
        return 0


class TupleEqTests(unittest.TestCase):

    def test_reference_component_uses_identity(self):
        a, b = Overriding(), Overriding()
        # The components compare equal under ==, which is exactly what must not be used.
        self.assertEqual(a, b)
        self.assertFalse(_dafny.tuple_eq((a, 1), (b, 1), (True, False)))
        self.assertTrue(_dafny.tuple_eq((a, 1), (a, 1), (True, False)))

    def test_value_component_uses_equality(self):
        a = Overriding()
        self.assertFalse(_dafny.tuple_eq((a, 1), (a, 2), (True, False)))
        self.assertTrue(_dafny.tuple_eq((1, 2), (1, 2), (False, False)))

    def test_nested_mask_recurses(self):
        a, b = Overriding(), Overriding()
        mask = (True, (True, False))
        self.assertTrue(_dafny.tuple_eq((a, (b, 2)), (a, (b, 2)), mask))
        self.assertFalse(_dafny.tuple_eq((a, (a, 2)), (a, (b, 2)), mask))
        self.assertFalse(_dafny.tuple_eq((a, (b, 2)), (a, (b, 3)), mask))

    def test_nested_mask_is_not_confused_with_the_boolean(self):
        # A one-element nested mask is a tuple, so it must not be read as True.
        a, b = Overriding(), Overriding()
        self.assertFalse(_dafny.tuple_eq(((a,), 1), ((b,), 1), ((True,), False)))
        self.assertTrue(_dafny.tuple_eq(((a,), 1), ((a,), 1), ((True,), False)))

    def test_differing_lengths(self):
        self.assertFalse(_dafny.tuple_eq((1, 2), (1, 2, 3), (False, False)))

    def test_comparator_is_cached_per_mask(self):
        # The emitted call sits wherever the comparison does, so the comparator is
        # cached to avoid building a closure per comparison.
        self.assertIs(_dafny.tuple_eq_by((True, False)), _dafny.tuple_eq_by((True, False)))

    def test_comparator_matches_tuple_eq(self):
        a, b = Overriding(), Overriding()
        compare = _dafny.tuple_eq_by((True, False))
        self.assertFalse(compare((a, 1), (b, 1)))
        self.assertTrue(compare((a, 1), (a, 1)))


if __name__ == "__main__":
    unittest.main()
