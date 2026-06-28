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
    break;
    if i > 0 {
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
method {:test} Test1() {
var seqint0 : seq<int> := [];
var r0 := intersperse(seqint0, 0);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [0];
var r0 := intersperse(seqint0, 0);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var r0 := intersperse(seqint0, 0);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, -100);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == -100;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 100);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 100;
}

// REPEAT 1 - TIME: 10.3873767 s

method {:test} Test12() {
var seqint0 : seq<int> := [3, 1, 0, 0];
var r0 := intersperse(seqint0, 24);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 24;
}

// REPEAT 2 - TIME: 11.2606737 s

method {:test} Test13() {
var seqint0 : seq<int> := [7, 2, 0, 0, 5, 0, 0, 0];
var r0 := intersperse(seqint0, 25);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 25;
}

// REPEAT 3 - TIME: 12.2536082 s

method {:test} Test14() {
var seqint0 : seq<int> := [4, 0, 0, 0, 0, 0, 0, 0, 8];
var r0 := intersperse(seqint0, 26);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 26;
}

// REPEAT 4 - TIME: 13.1447999 s

method {:test} Test15() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 10];
var r0 := intersperse(seqint0, 27);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 27;
}

// REPEAT 5 - TIME: 14.1722344 s

method {:test} Test16() {
var seqint0 : seq<int> := [9, 0, 0];
var r0 := intersperse(seqint0, 28);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 28;
}

// REPEAT 6 - TIME: 15.1198746 s

method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 29);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 29;
}

// REPEAT 7 - TIME: 16.1980133 s

method {:test} Test18() {
var seqint0 : seq<int> := [14, 0, 0, 0, 0, 12, 16];
var r0 := intersperse(seqint0, 30);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 30;
}

// REPEAT 8 - TIME: 17.1728419 s

method {:test} Test19() {
var seqint0 : seq<int> := [23, 0, 13, 0, 0, 19, 17, 21];
var r0 := intersperse(seqint0, 31);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 31;
}

// REPEAT 9 - TIME: 18.2457459 s

method {:test} Test20() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 24, 20, 26, 0];
var r0 := intersperse(seqint0, 32);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 32;
}

// REPEAT 10 - TIME: 19.293636 s
