This code was created using Dafny 4.2 in order to capture the existing code that
`--legacy-data-constructors` needs to still satisfy:

```
dafny translate java --output=fromDafny42/usesTimesTwo --allow-warnings --library=Inputs/producer/timesTwo.dfy usesTimesTwo.dfy
```