method m()
{
   var p := [2,3,1,0];
   assert forall i :: i in p ==> 0 <= i < |s|;
}