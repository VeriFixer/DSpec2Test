// dafny-synthesis_task_id_557.dfy

predicate IsLowerCase(c: char)
{
  97 <= c as int <= 122
}

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

predicate IsLowerUpperPair(c: char, C: char)
{
  c as int == C as int + 32
}

predicate IsUpperLowerPair(C: char, c: char)
{
  C as int == c as int - 32
}

function ShiftMinus32(c: char): char
{
  ((c as int - 32) % 128) as char
}

function Shift32(c: char): char
{
  ((c as int + 32) % 128) as char
}

method {:testEntry} ToggleCase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) && !IsUpperCase(s[k]) ==> s[k] == s'[k]
  {
    if IsLowerCase(s[i]) {
      s' := s';
    } else if IsUpperCase(s[i]) {
      s' := s';
    } else {
      s' := s';
    }
  }
  return s';
}


predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method {:testEntry} ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i &&  IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) && !IsUpperCase(s[k]) ==> s[k] == s'[k]
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
        }
        else if IsUpperCase(s[i])
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
var r0 := ToggleCase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test2() {
var r0 := ToggleCase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test3() {
var r0 := ToggleCase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsLowerCase("aa"[i]) then IsLowerUpperPair("aa"[i], r0[i]) else if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 1 - TIME: 8.0136045 s

method {:test} Test10() {
var r0 := ToggleCase("d&");
expect |r0| == |"d&"|;
expect forall i :: 0 <= i < |"d&"| ==> if IsLowerCase("d&"[i]) then IsLowerUpperPair("d&"[i], r0[i]) else if IsUpperCase("d&"[i]) then IsUpperLowerPair("d&"[i], r0[i]) else r0[i] == "d&"[i];
}

// REPEAT 2 - TIME: 8.8789701 s

method {:test} Test11() {
var r0 := ToggleCase("&@a");
expect |r0| == |"&@a"|;
expect forall i :: 0 <= i < |"&@a"| ==> if IsLowerCase("&@a"[i]) then IsLowerUpperPair("&@a"[i], r0[i]) else if IsUpperCase("&@a"[i]) then IsUpperLowerPair("&@a"[i], r0[i]) else r0[i] == "&@a"[i];
}

// REPEAT 3 - TIME: 9.7124991 s

method {:test} Test12() {
var r0 := ToggleCase("{\U{001A}1");
expect |r0| == |"{\U{001A}1"|;
expect forall i :: 0 <= i < |"{\U{001A}1"| ==> if IsLowerCase("{\U{001A}1"[i]) then IsLowerUpperPair("{\U{001A}1"[i], r0[i]) else if IsUpperCase("{\U{001A}1"[i]) then IsUpperLowerPair("{\U{001A}1"[i], r0[i]) else r0[i] == "{\U{001A}1"[i];
}

// REPEAT 4 - TIME: 10.5776628 s

method {:test} Test13() {
var r0 := ToggleCase(" aaaaaaaaaa aa-");
expect |r0| == |" aaaaaaaaaa aa-"|;
expect forall i :: 0 <= i < |" aaaaaaaaaa aa-"| ==> if IsLowerCase(" aaaaaaaaaa aa-"[i]) then IsLowerUpperPair(" aaaaaaaaaa aa-"[i], r0[i]) else if IsUpperCase(" aaaaaaaaaa aa-"[i]) then IsUpperLowerPair(" aaaaaaaaaa aa-"[i], r0[i]) else r0[i] == " aaaaaaaaaa aa-"[i];
}

// REPEAT 5 - TIME: 11.4901754 s

method {:test} Test14() {
var r0 := ToggleCase("!aaaaaaaaaaaaaa-");
expect |r0| == |"!aaaaaaaaaaaaaa-"|;
expect forall i :: 0 <= i < |"!aaaaaaaaaaaaaa-"| ==> if IsLowerCase("!aaaaaaaaaaaaaa-"[i]) then IsLowerUpperPair("!aaaaaaaaaaaaaa-"[i], r0[i]) else if IsUpperCase("!aaaaaaaaaaaaaa-"[i]) then IsUpperLowerPair("!aaaaaaaaaaaaaa-"[i], r0[i]) else r0[i] == "!aaaaaaaaaaaaaa-"[i];
}

// REPEAT 6 - TIME: 12.4605895 s

method {:test} Test15() {
var r0 := ToggleCase("a\U{001A}a1");
expect |r0| == |"a\U{001A}a1"|;
expect forall i :: 0 <= i < |"a\U{001A}a1"| ==> if IsLowerCase("a\U{001A}a1"[i]) then IsLowerUpperPair("a\U{001A}a1"[i], r0[i]) else if IsUpperCase("a\U{001A}a1"[i]) then IsUpperLowerPair("a\U{001A}a1"[i], r0[i]) else r0[i] == "a\U{001A}a1"[i];
}

// REPEAT 7 - TIME: 13.4633336 s

method {:test} Test16() {
var r0 := ToggleCase("\U{000F}\U{001A}aa0aaaaaaaaaa ");
expect |r0| == |"\U{000F}\U{001A}aa0aaaaaaaaaa "|;
expect forall i :: 0 <= i < |"\U{000F}\U{001A}aa0aaaaaaaaaa "| ==> if IsLowerCase("\U{000F}\U{001A}aa0aaaaaaaaaa "[i]) then IsLowerUpperPair("\U{000F}\U{001A}aa0aaaaaaaaaa "[i], r0[i]) else if IsUpperCase("\U{000F}\U{001A}aa0aaaaaaaaaa "[i]) then IsUpperLowerPair("\U{000F}\U{001A}aa0aaaaaaaaaa "[i], r0[i]) else r0[i] == "\U{000F}\U{001A}aa0aaaaaaaaaa "[i];
}

// REPEAT 8 - TIME: 14.5038804 s

method {:test} Test17() {
var r0 := ToggleCase("g aaaa");
expect |r0| == |"g aaaa"|;
expect forall i :: 0 <= i < |"g aaaa"| ==> if IsLowerCase("g aaaa"[i]) then IsLowerUpperPair("g aaaa"[i], r0[i]) else if IsUpperCase("g aaaa"[i]) then IsUpperLowerPair("g aaaa"[i], r0[i]) else r0[i] == "g aaaa"[i];
}

// REPEAT 9 - TIME: 15.4059516 s

method {:test} Test18() {
var r0 := ToggleCase("\U{001A}aaaa");
expect |r0| == |"\U{001A}aaaa"|;
expect forall i :: 0 <= i < |"\U{001A}aaaa"| ==> if IsLowerCase("\U{001A}aaaa"[i]) then IsLowerUpperPair("\U{001A}aaaa"[i], r0[i]) else if IsUpperCase("\U{001A}aaaa"[i]) then IsUpperLowerPair("\U{001A}aaaa"[i], r0[i]) else r0[i] == "\U{001A}aaaa"[i];
}

// REPEAT 10 - TIME: 16.1090632 s
