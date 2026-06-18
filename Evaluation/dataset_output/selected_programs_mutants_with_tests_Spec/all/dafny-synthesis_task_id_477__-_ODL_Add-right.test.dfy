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
      s' := s';
    } else {
      s' := s';
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

// REPEAT 1 - TIME: 2.9775551 s

method {:test} Test1() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 2 - TIME: 4.109576 s

method {:test} Test2() {
var r0 := ToLowercase("a@aaaaaaaaaaaaaaaaaaa0");
expect |r0| == |"a@aaaaaaaaaaaaaaaaaaa0"|;
expect forall i :: 0 <= i < |"a@aaaaaaaaaaaaaaaaaaa0"| ==> if IsUpperCase("a@aaaaaaaaaaaaaaaaaaa0"[i]) then IsUpperLowerPair("a@aaaaaaaaaaaaaaaaaaa0"[i], r0[i]) else r0[i] == "a@aaaaaaaaaaaaaaaaaaa0"[i];
}

// REPEAT 3 - TIME: 5.384281 s

method {:test} Test3() {
var r0 := ToLowercase("01a");
expect |r0| == |"01a"|;
expect forall i :: 0 <= i < |"01a"| ==> if IsUpperCase("01a"[i]) then IsUpperLowerPair("01a"[i], r0[i]) else r0[i] == "01a"[i];
}

// REPEAT 4 - TIME: 6.5184722 s

method {:test} Test4() {
var r0 := ToLowercase("a\U{0010}aaaaaaaaaaaaaaaaaaaa ");
expect |r0| == |"a\U{0010}aaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"a\U{0010}aaaaaaaaaaaaaaaaaaaa "| ==> if IsUpperCase("a\U{0010}aaaaaaaaaaaaaaaaaaaa "[i]) then IsUpperLowerPair("a\U{0010}aaaaaaaaaaaaaaaaaaaa "[i], r0[i]) else r0[i] == "a\U{0010}aaaaaaaaaaaaaaaaaaaa "[i];
}

// REPEAT 5 - TIME: 7.7091511 s

method {:test} Test5() {
var r0 := ToLowercase(" \U{000F}aaa0");
expect |r0| == |" \U{000F}aaa0"|;
expect forall i :: 0 <= i < |" \U{000F}aaa0"| ==> if IsUpperCase(" \U{000F}aaa0"[i]) then IsUpperLowerPair(" \U{000F}aaa0"[i], r0[i]) else r0[i] == " \U{000F}aaa0"[i];
}

// REPEAT 6 - TIME: 8.8837898 s

method {:test} Test6() {
var r0 := ToLowercase("1a");
expect |r0| == |"1a"|;
expect forall i :: 0 <= i < |"1a"| ==> if IsUpperCase("1a"[i]) then IsUpperLowerPair("1a"[i], r0[i]) else r0[i] == "1a"[i];
}

// REPEAT 7 - TIME: 9.7005951 s

method {:test} Test7() {
var r0 := ToLowercase(" aa\U{000F}");
expect |r0| == |" aa\U{000F}"|;
expect forall i :: 0 <= i < |" aa\U{000F}"| ==> if IsUpperCase(" aa\U{000F}"[i]) then IsUpperLowerPair(" aa\U{000F}"[i], r0[i]) else r0[i] == " aa\U{000F}"[i];
}

// REPEAT 8 - TIME: 10.4079464 s

method {:test} Test8() {
var r0 := ToLowercase(".-");
expect |r0| == |".-"|;
expect forall i :: 0 <= i < |".-"| ==> if IsUpperCase(".-"[i]) then IsUpperLowerPair(".-"[i], r0[i]) else r0[i] == ".-"[i];
}

// REPEAT 9 - TIME: 11.1312425 s

method {:test} Test9() {
var r0 := ToLowercase("0aaaaaa");
expect |r0| == |"0aaaaaa"|;
expect forall i :: 0 <= i < |"0aaaaaa"| ==> if IsUpperCase("0aaaaaa"[i]) then IsUpperLowerPair("0aaaaaa"[i], r0[i]) else r0[i] == "0aaaaaa"[i];
}

// REPEAT 10 - TIME: 11.7679017 s
