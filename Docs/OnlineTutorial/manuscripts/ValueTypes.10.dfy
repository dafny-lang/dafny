method m()
{
   var s := [1, 2, 3, 4, 5];
   assert s[|s|-1] == 5; //access the last element
   assert s[|s|-1..|s|] == [5]; //slice just the last element, as a singleton
   assert s[1..] == [2, 3, 4, 5]; // everything but the first
   assert s[..|s|-1] == [1, 2, 3, 4]; // everything but the last
   assert s == s[0..] == s[..|s|] == s[0..|s|]; // the whole sequence
}