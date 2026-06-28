// llm-verified-eval_tmp_tmpd2deqn_i_dafny_5.dfy

method {:testEntry} intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
  ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
  ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> interspersed[i] == numbers[i / 2]
  ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==> interspersed[i] == delimiter
{
  interspersed := [];
  for i := 0 to |numbers|
    invariant |interspersed| == if i > 0 then 2 * i - 1 else 0
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 0 ==> interspersed[i0] == numbers[i0 / 2]
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 1 ==> interspersed[i0] == delimiter
  {
    if i >= 0 {
      interspersed := interspersed + [delimiter];
    }
    interspersed := interspersed + [numbers[i]];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 0);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 0;
}

// REPEAT 1 - TIME: 2.9720433 s

method {:test} Test1() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 24);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 24;
}

// REPEAT 2 - TIME: 3.945943 s

method {:test} Test2() {
var seqint0 : seq<int> := [2, 0];
var r0 := intersperse(seqint0, 25);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 25;
}

// REPEAT 3 - TIME: 4.9887157 s

method {:test} Test3() {
var seqint0 : seq<int> := [3, 0];
var r0 := intersperse(seqint0, 26);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 26;
}

// REPEAT 4 - TIME: 6.0153365 s

method {:test} Test4() {
var seqint0 : seq<int> := [4, 0, 6];
var r0 := intersperse(seqint0, 27);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 27;
}

// REPEAT 5 - TIME: 7.0996173 s

method {:test} Test5() {
var seqint0 : seq<int> := [5, 0, 8];
var r0 := intersperse(seqint0, 28);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 28;
}

// REPEAT 6 - TIME: 8.1457449 s

method {:test} Test6() {
var seqint0 : seq<int> := [7];
var r0 := intersperse(seqint0, 29);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 29;
}

// REPEAT 7 - TIME: 9.2464075 s

method {:test} Test7() {
var seqint0 : seq<int> := [13, 0, 9, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 31);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 31;
}

// REPEAT 8 - TIME: 10.2950102 s

method {:test} Test8() {
var seqint0 : seq<int> := [14, 0, 0, 10, 0, 0, 0, 18, 0, 0, 16, 0];
var r0 := intersperse(seqint0, 30);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 30;
}

// REPEAT 9 - TIME: 11.0804876 s

method {:test} Test9() {
var seqint0 : seq<int> := [17, 12];
var r0 := intersperse(seqint0, 32);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 32;
}

// REPEAT 10 - TIME: 11.779909 s
