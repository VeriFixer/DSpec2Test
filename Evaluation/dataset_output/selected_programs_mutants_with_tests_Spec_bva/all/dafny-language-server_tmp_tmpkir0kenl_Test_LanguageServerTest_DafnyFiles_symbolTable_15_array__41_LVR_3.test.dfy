// dafny-language-server_tmp_tmpkir0kenl_Test_LanguageServerTest_DafnyFiles_symbolTable_15_array.dfy

method {:testEntry} Main()
{
  var i := 3;
  var s := [1, i, 3, 4, 5];
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


method {:test} Test0() {
Main();
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 1 - TIME: 6.809659 s

method {:test} Test7() {
var seqint0 : seq<int> := [1, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 2 - TIME: 7.983646 s

method {:test} Test8() {
var seqint0 : seq<int> := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 3 - TIME: 9.1322587 s

method {:test} Test9() {
var seqint0 : seq<int> := [3, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 4 - TIME: 10.5496289 s

method {:test} Test10() {
var seqint0 : seq<int> := [5, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 5 - TIME: 11.5008394 s

method {:test} Test11() {
var seqint0 : seq<int> := [6, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 6 - TIME: 12.4581029 s

method {:test} Test12() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 9];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 7 - TIME: 13.1875151 s

method {:test} Test13() {
var seqint0 : seq<int> := [8, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 8 - TIME: 13.979877 s

method {:test} Test14() {
var seqint0 : seq<int> := [10, 0, 0, 0, 12];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 9 - TIME: 14.7399975 s

method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 11, 16];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
foo(seqint0);
}

// REPEAT 10 - TIME: 15.3837175 s
