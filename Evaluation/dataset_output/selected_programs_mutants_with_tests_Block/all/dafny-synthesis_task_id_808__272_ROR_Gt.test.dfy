// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if s[i] > k {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 26];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}

// REPEAT 1 - TIME: 2.7711143 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 27];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}

// REPEAT 2 - TIME: 3.7717617 s

method {:test} Test2() {
var seqint0 : seq<int> := [28, 39];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}

// REPEAT 3 - TIME: 4.7730253 s

method {:test} Test3() {
var seqint0 : seq<int> := [45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 29];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}

// REPEAT 4 - TIME: 5.6497094 s

method {:test} Test4() {
var seqint0 : seq<int> := [32, 68, 65];
var r0 := ContainsK(seqint0, 32);
expect r0 <==> 32 in seqint0;
}

// REPEAT 5 - TIME: 6.7007416 s

method {:test} Test5() {
var seqint0 : seq<int> := [72];
var r0 := ContainsK(seqint0, 72);
expect r0 <==> 72 in seqint0;
}

// REPEAT 6 - TIME: 7.748262 s

method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 33, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4];
var r0 := ContainsK(seqint0, 33);
expect r0 <==> 33 in seqint0;
}

// REPEAT 7 - TIME: 8.6739864 s

method {:test} Test7() {
var seqint0 : seq<int> := [30, 3, 0, 0, 0, 0, 0, 8, 0, 6, 0, 0, 0, 0, 0, 0, 0, 10];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}

// REPEAT 8 - TIME: 9.5090156 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 112, 0, 0, 31, 108];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}

// REPEAT 9 - TIME: 10.2628782 s

method {:test} Test9() {
var seqint0 : seq<int> := [123, 113, 0, 0, 0, 0, 0, 117, 0, 114, 0, 0, 0, 0, 0, 0, 0, 34, 118];
var r0 := ContainsK(seqint0, 34);
expect r0 <==> 34 in seqint0;
}

// REPEAT 10 - TIME: 11.0983166 s
