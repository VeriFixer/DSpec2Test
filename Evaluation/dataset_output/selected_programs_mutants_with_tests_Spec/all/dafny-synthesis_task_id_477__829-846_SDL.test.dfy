// dafny-synthesis_task_id_477.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

predicate IsUpperLowerPair(C: char, c: char)
{
  C as int == c as int - 32
}

function Shift32(c: char): char
{
  ((c as int + 32) % 128) as char
}

method {:testEntry} ToLowercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsUpperCase(s[k]) ==> s[k] == s'[k]
  {
    if IsUpperCase(s[i]) {
      s' := s' + [Shift32(s[i])];
    } else {
    }
  }
  return s';
}


predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method {:testEntry} ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsUpperCase(s[k]) ==> s[k] == s'[k]
    {
        if IsUpperCase(s[i])
        {
            s' := s' + [Shift32(s[i])];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test0() {
var r0 := ToLowercase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}

// REPEAT 1 - TIME: 3.0334985 s

method {:test} Test1() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 2 - TIME: 4.0612575 s

method {:test} Test2() {
var r0 := ToLowercase("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0");
expect |r0| == |"a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"|;
expect forall i :: 0 <= i < |"a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"| ==> if IsUpperCase("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i]) then IsUpperLowerPair("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i], r0[i]) else r0[i] == "a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i];
}

// REPEAT 3 - TIME: 5.0381892 s

method {:test} Test3() {
var r0 := ToLowercase("0\U{001A}");
expect |r0| == |"0\U{001A}"|;
expect forall i :: 0 <= i < |"0\U{001A}"| ==> if IsUpperCase("0\U{001A}"[i]) then IsUpperLowerPair("0\U{001A}"[i], r0[i]) else r0[i] == "0\U{001A}"[i];
}

// REPEAT 4 - TIME: 6.0860522 s

method {:test} Test4() {
var r0 := ToLowercase(" \U{001A}");
expect |r0| == |" \U{001A}"|;
expect forall i :: 0 <= i < |" \U{001A}"| ==> if IsUpperCase(" \U{001A}"[i]) then IsUpperLowerPair(" \U{001A}"[i], r0[i]) else r0[i] == " \U{001A}"[i];
}

// REPEAT 5 - TIME: 6.9690923 s

method {:test} Test5() {
var r0 := ToLowercase("0\U{001A}1");
expect |r0| == |"0\U{001A}1"|;
expect forall i :: 0 <= i < |"0\U{001A}1"| ==> if IsUpperCase("0\U{001A}1"[i]) then IsUpperLowerPair("0\U{001A}1"[i], r0[i]) else r0[i] == "0\U{001A}1"[i];
}

// REPEAT 6 - TIME: 7.9445601 s

method {:test} Test6() {
var r0 := ToLowercase(" aa0");
expect |r0| == |" aa0"|;
expect forall i :: 0 <= i < |" aa0"| ==> if IsUpperCase(" aa0"[i]) then IsUpperLowerPair(" aa0"[i], r0[i]) else r0[i] == " aa0"[i];
}

// REPEAT 7 - TIME: 8.792243 s

method {:test} Test7() {
var r0 := ToLowercase("6 a");
expect |r0| == |"6 a"|;
expect forall i :: 0 <= i < |"6 a"| ==> if IsUpperCase("6 a"[i]) then IsUpperLowerPair("6 a"[i], r0[i]) else r0[i] == "6 a"[i];
}

// REPEAT 8 - TIME: 9.5311547 s

method {:test} Test8() {
var r0 := ToLowercase("\U{0014}1- \U{0003}");
expect |r0| == |"\U{0014}1- \U{0003}"|;
expect forall i :: 0 <= i < |"\U{0014}1- \U{0003}"| ==> if IsUpperCase("\U{0014}1- \U{0003}"[i]) then IsUpperLowerPair("\U{0014}1- \U{0003}"[i], r0[i]) else r0[i] == "\U{0014}1- \U{0003}"[i];
}

// REPEAT 9 - TIME: 10.3081486 s

method {:test} Test9() {
var r0 := ToLowercase("a\U{0010}aa  ");
expect |r0| == |"a\U{0010}aa  "|;
expect forall i :: 0 <= i < |"a\U{0010}aa  "| ==> if IsUpperCase("a\U{0010}aa  "[i]) then IsUpperLowerPair("a\U{0010}aa  "[i], r0[i]) else r0[i] == "a\U{0010}aa  "[i];
}

// REPEAT 10 - TIME: 11.0653803 s
