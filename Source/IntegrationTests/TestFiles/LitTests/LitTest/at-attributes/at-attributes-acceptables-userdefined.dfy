// Attribute to use anywhere
@Attribute
datatype CustomAttribute = CustomAttribute

@CustomAttribute
datatype CustomDeclarationAttribute = CustomDeclarationAttribute(@CustomAttribute n: string)

method OtherUserDefinedAttributes()
  @CustomAttribute
  decreases *
{
  @CustomAttribute
  calc {
    1;
    1;
  }
  while true
    @CustomAttribute
    invariant true
  {
  }
}