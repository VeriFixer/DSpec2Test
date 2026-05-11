//../Binaries/dafny generate-tests Spec "Example2.dfy" > "Example2Tests.dfy"

method MatchFirst(s1: seq<int>, s2: seq<int>) returns (isMatch: bool)
  ensures isMatch == (|s1| == 0 || |s2| == 0 || s1[0] == s2[0])
{
  return |s1| == 1 || |s2| == 0 || s1[0] == s2[0];
}

