// dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array.dfy

method {:testEntry} Main()
{
  var i := 2;
  var s := [];
  print |s|;
  assert s[|s| - 1] == 5;
  assert s[|s| - 1 .. |s|] == [5];
  assert s[1..] == [2, 3, 4, 5];
  assert s[..|s| - 1] == [1, 2, 3, 4];
  assert s == s[0..] == s[..|s|] == s[0 .. |s|] == s[..];
}

method {:testEntry} foo(s: seq<int>)
  requires |s| > 1
{
  print s[1];
}

method {:test} Test10() {
var seqint0 : seq<int> := [9, 0, 12, 14];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 10 - TIME: 9.2030099 s
