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
    break;
    if IsUpperCase(s[i]) {
      s' := s' + [Shift32(s[i])];
    } else {
      s' := s' + [s[i]];
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
method {:test} Test1() {
var r0 := ToLowercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test3() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 1 - TIME: 7.9566983 s

method {:test} Test10() {
var r0 := ToLowercase("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0");
expect |r0| == |"a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"|;
expect forall i :: 0 <= i < |"a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"| ==> if IsUpperCase("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i]) then IsUpperLowerPair("a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i], r0[i]) else r0[i] == "a@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0"[i];
}

// REPEAT 2 - TIME: 8.8550103 s

method {:test} Test11() {
var r0 := ToLowercase("0\U{001A}1");
expect |r0| == |"0\U{001A}1"|;
expect forall i :: 0 <= i < |"0\U{001A}1"| ==> if IsUpperCase("0\U{001A}1"[i]) then IsUpperLowerPair("0\U{001A}1"[i], r0[i]) else r0[i] == "0\U{001A}1"[i];
}

// REPEAT 3 - TIME: 9.6851425 s

method {:test} Test12() {
var r0 := ToLowercase("0a");
expect |r0| == |"0a"|;
expect forall i :: 0 <= i < |"0a"| ==> if IsUpperCase("0a"[i]) then IsUpperLowerPair("0a"[i], r0[i]) else r0[i] == "0a"[i];
}

// REPEAT 4 - TIME: 10.5409905 s

method {:test} Test13() {
var r0 := ToLowercase("\U{001A}aa");
expect |r0| == |"\U{001A}aa"|;
expect forall i :: 0 <= i < |"\U{001A}aa"| ==> if IsUpperCase("\U{001A}aa"[i]) then IsUpperLowerPair("\U{001A}aa"[i], r0[i]) else r0[i] == "\U{001A}aa"[i];
}

// REPEAT 5 - TIME: 11.3167327 s

method {:test} Test14() {
var r0 := ToLowercase("aa aaaa \U{000F}");
expect |r0| == |"aa aaaa \U{000F}"|;
expect forall i :: 0 <= i < |"aa aaaa \U{000F}"| ==> if IsUpperCase("aa aaaa \U{000F}"[i]) then IsUpperLowerPair("aa aaaa \U{000F}"[i], r0[i]) else r0[i] == "aa aaaa \U{000F}"[i];
}

// REPEAT 6 - TIME: 12.1856791 s

method {:test} Test15() {
var r0 := ToLowercase("-\U{0010}aaaa\U{000F}a  ");
expect |r0| == |"-\U{0010}aaaa\U{000F}a  "|;
expect forall i :: 0 <= i < |"-\U{0010}aaaa\U{000F}a  "| ==> if IsUpperCase("-\U{0010}aaaa\U{000F}a  "[i]) then IsUpperLowerPair("-\U{0010}aaaa\U{000F}a  "[i], r0[i]) else r0[i] == "-\U{0010}aaaa\U{000F}a  "[i];
}

// REPEAT 7 - TIME: 13.1607487 s

method {:test} Test16() {
var r0 := ToLowercase("aaaaaaaa  -");
expect |r0| == |"aaaaaaaa  -"|;
expect forall i :: 0 <= i < |"aaaaaaaa  -"| ==> if IsUpperCase("aaaaaaaa  -"[i]) then IsUpperLowerPair("aaaaaaaa  -"[i], r0[i]) else r0[i] == "aaaaaaaa  -"[i];
}

// REPEAT 8 - TIME: 13.8004325 s

method {:test} Test17() {
var r0 := ToLowercase("-aaaa aaa0 -");
expect |r0| == |"-aaaa aaa0 -"|;
expect forall i :: 0 <= i < |"-aaaa aaa0 -"| ==> if IsUpperCase("-aaaa aaa0 -"[i]) then IsUpperLowerPair("-aaaa aaa0 -"[i], r0[i]) else r0[i] == "-aaaa aaa0 -"[i];
}

// REPEAT 9 - TIME: 14.5999585 s

method {:test} Test18() {
var r0 := ToLowercase("\U{001A}\U{001B}aa");
expect |r0| == |"\U{001A}\U{001B}aa"|;
expect forall i :: 0 <= i < |"\U{001A}\U{001B}aa"| ==> if IsUpperCase("\U{001A}\U{001B}aa"[i]) then IsUpperLowerPair("\U{001A}\U{001B}aa"[i], r0[i]) else r0[i] == "\U{001A}\U{001B}aa"[i];
}

// REPEAT 10 - TIME: 15.3577669 s
