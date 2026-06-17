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
      s' := s' + [ShiftMinus32(s[i])];
    } else if IsUpperCase(s[i]) {
      s' := s' + [Shift32(s[i])];
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
var r0 := ToggleCase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test5() {
var r0 := ToggleCase("a`");
expect |r0| == |"a`"|;
expect forall i :: 0 <= i < |"a`"| ==> if IsLowerCase("a`"[i]) then IsLowerUpperPair("a`"[i], r0[i]) else if IsUpperCase("a`"[i]) then IsUpperLowerPair("a`"[i], r0[i]) else r0[i] == "a`"[i];
}

// REPEAT 1 - TIME: 5.4057073 s

method {:test} Test6() {
var r0 := ToggleCase("aa@");
expect |r0| == |"aa@"|;
expect forall i :: 0 <= i < |"aa@"| ==> if IsLowerCase("aa@"[i]) then IsLowerUpperPair("aa@"[i], r0[i]) else if IsUpperCase("aa@"[i]) then IsUpperLowerPair("aa@"[i], r0[i]) else r0[i] == "aa@"[i];
}
method {:test} Test7() {
var r0 := ToggleCase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test8() {
var r0 := ToggleCase("afc");
expect |r0| == |"afc"|;
expect forall i :: 0 <= i < |"afc"| ==> if IsLowerCase("afc"[i]) then IsLowerUpperPair("afc"[i], r0[i]) else if IsUpperCase("afc"[i]) then IsUpperLowerPair("afc"[i], r0[i]) else r0[i] == "afc"[i];
}
method {:test} Test9() {
var r0 := ToggleCase("a{\U{000F}");
expect |r0| == |"a{\U{000F}"|;
expect forall i :: 0 <= i < |"a{\U{000F}"| ==> if IsLowerCase("a{\U{000F}"[i]) then IsLowerUpperPair("a{\U{000F}"[i], r0[i]) else if IsUpperCase("a{\U{000F}"[i]) then IsUpperLowerPair("a{\U{000F}"[i], r0[i]) else r0[i] == "a{\U{000F}"[i];
}
method {:test} Test10() {
var r0 := ToggleCase("k");
expect |r0| == |"k"|;
expect forall i :: 0 <= i < |"k"| ==> if IsLowerCase("k"[i]) then IsLowerUpperPair("k"[i], r0[i]) else if IsUpperCase("k"[i]) then IsUpperLowerPair("k"[i], r0[i]) else r0[i] == "k"[i];
}
method {:test} Test11() {
var r0 := ToggleCase("C{");
expect |r0| == |"C{"|;
expect forall i :: 0 <= i < |"C{"| ==> if IsLowerCase("C{"[i]) then IsLowerUpperPair("C{"[i], r0[i]) else if IsUpperCase("C{"[i]) then IsUpperLowerPair("C{"[i], r0[i]) else r0[i] == "C{"[i];
}

// REPEAT 2 - TIME: 9.4921245 s

method {:test} Test12() {
var r0 := ToggleCase("kaag");
expect |r0| == |"kaag"|;
expect forall i :: 0 <= i < |"kaag"| ==> if IsLowerCase("kaag"[i]) then IsLowerUpperPair("kaag"[i], r0[i]) else if IsUpperCase("kaag"[i]) then IsUpperLowerPair("kaag"[i], r0[i]) else r0[i] == "kaag"[i];
}
method {:test} Test13() {
var r0 := ToggleCase("[C\U{0015}a");
expect |r0| == |"[C\U{0015}a"|;
expect forall i :: 0 <= i < |"[C\U{0015}a"| ==> if IsLowerCase("[C\U{0015}a"[i]) then IsLowerUpperPair("[C\U{0015}a"[i], r0[i]) else if IsUpperCase("[C\U{0015}a"[i]) then IsUpperLowerPair("[C\U{0015}a"[i], r0[i]) else r0[i] == "[C\U{0015}a"[i];
}
method {:test} Test14() {
var r0 := ToggleCase("sa");
expect |r0| == |"sa"|;
expect forall i :: 0 <= i < |"sa"| ==> if IsLowerCase("sa"[i]) then IsLowerUpperPair("sa"[i], r0[i]) else if IsUpperCase("sa"[i]) then IsUpperLowerPair("sa"[i], r0[i]) else r0[i] == "sa"[i];
}
method {:test} Test15() {
var r0 := ToggleCase("-");
expect |r0| == |"-"|;
expect forall i :: 0 <= i < |"-"| ==> if IsLowerCase("-"[i]) then IsLowerUpperPair("-"[i], r0[i]) else if IsUpperCase("-"[i]) then IsUpperLowerPair("-"[i], r0[i]) else r0[i] == "-"[i];
}
method {:test} Test16() {
var r0 := ToggleCase("araa");
expect |r0| == |"araa"|;
expect forall i :: 0 <= i < |"araa"| ==> if IsLowerCase("araa"[i]) then IsLowerUpperPair("araa"[i], r0[i]) else if IsUpperCase("araa"[i]) then IsUpperLowerPair("araa"[i], r0[i]) else r0[i] == "araa"[i];
}
method {:test} Test17() {
var r0 := ToggleCase("g\U{0004}bg");
expect |r0| == |"g\U{0004}bg"|;
expect forall i :: 0 <= i < |"g\U{0004}bg"| ==> if IsLowerCase("g\U{0004}bg"[i]) then IsLowerUpperPair("g\U{0004}bg"[i], r0[i]) else if IsUpperCase("g\U{0004}bg"[i]) then IsUpperLowerPair("g\U{0004}bg"[i], r0[i]) else r0[i] == "g\U{0004}bg"[i];
}

// REPEAT 3 - TIME: 12.4426335 s

method {:test} Test18() {
var r0 := ToggleCase("gacayaaaajqa");
expect |r0| == |"gacayaaaajqa"|;
expect forall i :: 0 <= i < |"gacayaaaajqa"| ==> if IsLowerCase("gacayaaaajqa"[i]) then IsLowerUpperPair("gacayaaaajqa"[i], r0[i]) else if IsUpperCase("gacayaaaajqa"[i]) then IsUpperLowerPair("gacayaaaajqa"[i], r0[i]) else r0[i] == "gacayaaaajqa"[i];
}
method {:test} Test19() {
var r0 := ToggleCase("Kaa");
expect |r0| == |"Kaa"|;
expect forall i :: 0 <= i < |"Kaa"| ==> if IsLowerCase("Kaa"[i]) then IsLowerUpperPair("Kaa"[i], r0[i]) else if IsUpperCase("Kaa"[i]) then IsUpperLowerPair("Kaa"[i], r0[i]) else r0[i] == "Kaa"[i];
}
method {:test} Test20() {
var r0 := ToggleCase("7a");
expect |r0| == |"7a"|;
expect forall i :: 0 <= i < |"7a"| ==> if IsLowerCase("7a"[i]) then IsLowerUpperPair("7a"[i], r0[i]) else if IsUpperCase("7a"[i]) then IsUpperLowerPair("7a"[i], r0[i]) else r0[i] == "7a"[i];
}
method {:test} Test21() {
var r0 := ToggleCase(".");
expect |r0| == |"."|;
expect forall i :: 0 <= i < |"."| ==> if IsLowerCase("."[i]) then IsLowerUpperPair("."[i], r0[i]) else if IsUpperCase("."[i]) then IsUpperLowerPair("."[i], r0[i]) else r0[i] == "."[i];
}
method {:test} Test22() {
var r0 := ToggleCase("\U{0005}aa");
expect |r0| == |"\U{0005}aa"|;
expect forall i :: 0 <= i < |"\U{0005}aa"| ==> if IsLowerCase("\U{0005}aa"[i]) then IsLowerUpperPair("\U{0005}aa"[i], r0[i]) else if IsUpperCase("\U{0005}aa"[i]) then IsUpperLowerPair("\U{0005}aa"[i], r0[i]) else r0[i] == "\U{0005}aa"[i];
}
method {:test} Test23() {
var r0 := ToggleCase("bT\U{0004}\U{0006}\0");
expect |r0| == |"bT\U{0004}\U{0006}\0"|;
expect forall i :: 0 <= i < |"bT\U{0004}\U{0006}\0"| ==> if IsLowerCase("bT\U{0004}\U{0006}\0"[i]) then IsLowerUpperPair("bT\U{0004}\U{0006}\0"[i], r0[i]) else if IsUpperCase("bT\U{0004}\U{0006}\0"[i]) then IsUpperLowerPair("bT\U{0004}\U{0006}\0"[i], r0[i]) else r0[i] == "bT\U{0004}\U{0006}\0"[i];
}

// REPEAT 4 - TIME: 15.0877052 s

method {:test} Test24() {
var r0 := ToggleCase("gaabaaaaaacqa");
expect |r0| == |"gaabaaaaaacqa"|;
expect forall i :: 0 <= i < |"gaabaaaaaacqa"| ==> if IsLowerCase("gaabaaaaaacqa"[i]) then IsLowerUpperPair("gaabaaaaaacqa"[i], r0[i]) else if IsUpperCase("gaabaaaaaacqa"[i]) then IsUpperLowerPair("gaabaaaaaacqa"[i], r0[i]) else r0[i] == "gaabaaaaaacqa"[i];
}
method {:test} Test25() {
var r0 := ToggleCase("\U{D0FB}a");
expect |r0| == |"\U{D0FB}a"|;
expect forall i :: 0 <= i < |"\U{D0FB}a"| ==> if IsLowerCase("\U{D0FB}a"[i]) then IsLowerUpperPair("\U{D0FB}a"[i], r0[i]) else if IsUpperCase("\U{D0FB}a"[i]) then IsUpperLowerPair("\U{D0FB}a"[i], r0[i]) else r0[i] == "\U{D0FB}a"[i];
}
method {:test} Test26() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test27() {
var r0 := ToggleCase("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test28() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test29() {
var r0 := ToggleCase("Daa\U{0001}gg");
expect |r0| == |"Daa\U{0001}gg"|;
expect forall i :: 0 <= i < |"Daa\U{0001}gg"| ==> if IsLowerCase("Daa\U{0001}gg"[i]) then IsLowerUpperPair("Daa\U{0001}gg"[i], r0[i]) else if IsUpperCase("Daa\U{0001}gg"[i]) then IsUpperLowerPair("Daa\U{0001}gg"[i], r0[i]) else r0[i] == "Daa\U{0001}gg"[i];
}

// REPEAT 5 - TIME: 18.4786337 s

method {:test} Test30() {
var r0 := ToggleCase("gaaaaaa");
expect |r0| == |"gaaaaaa"|;
expect forall i :: 0 <= i < |"gaaaaaa"| ==> if IsLowerCase("gaaaaaa"[i]) then IsLowerUpperPair("gaaaaaa"[i], r0[i]) else if IsUpperCase("gaaaaaa"[i]) then IsUpperLowerPair("gaaaaaa"[i], r0[i]) else r0[i] == "gaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToggleCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test32() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test34() {
var r0 := ToggleCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToggleCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 6 - TIME: 21.7866653 s

method {:test} Test36() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test41() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaTaaaaaaaaaaaa\0aaaaaaaa"[i];
}

// REPEAT 7 - TIME: 25.058762 s

method {:test} Test42() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i];
}
method {:test} Test43() {
var r0 := ToggleCase("\U{000F}a");
expect |r0| == |"\U{000F}a"|;
expect forall i :: 0 <= i < |"\U{000F}a"| ==> if IsLowerCase("\U{000F}a"[i]) then IsLowerUpperPair("\U{000F}a"[i], r0[i]) else if IsUpperCase("\U{000F}a"[i]) then IsUpperLowerPair("\U{000F}a"[i], r0[i]) else r0[i] == "\U{000F}a"[i];
}
method {:test} Test44() {
var r0 := ToggleCase("\U{0007}a");
expect |r0| == |"\U{0007}a"|;
expect forall i :: 0 <= i < |"\U{0007}a"| ==> if IsLowerCase("\U{0007}a"[i]) then IsLowerUpperPair("\U{0007}a"[i], r0[i]) else if IsUpperCase("\U{0007}a"[i]) then IsUpperLowerPair("\U{0007}a"[i], r0[i]) else r0[i] == "\U{0007}a"[i];
}
method {:test} Test45() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test47() {
var r0 := ToggleCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 8 - TIME: 28.9372542 s

method {:test} Test48() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test51() {
var r0 := ToggleCase("Ya");
expect |r0| == |"Ya"|;
expect forall i :: 0 <= i < |"Ya"| ==> if IsLowerCase("Ya"[i]) then IsLowerUpperPair("Ya"[i], r0[i]) else if IsUpperCase("Ya"[i]) then IsUpperLowerPair("Ya"[i], r0[i]) else r0[i] == "Ya"[i];
}
method {:test} Test53() {
var r0 := ToggleCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 9 - TIME: 32.7428812 s

method {:test} Test54() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test55() {
var r0 := ToggleCase("\U{0010}a");
expect |r0| == |"\U{0010}a"|;
expect forall i :: 0 <= i < |"\U{0010}a"| ==> if IsLowerCase("\U{0010}a"[i]) then IsLowerUpperPair("\U{0010}a"[i], r0[i]) else if IsUpperCase("\U{0010}a"[i]) then IsUpperLowerPair("\U{0010}a"[i], r0[i]) else r0[i] == "\U{0010}a"[i];
}
method {:test} Test56() {
var r0 := ToggleCase("\U{0019}a");
expect |r0| == |"\U{0019}a"|;
expect forall i :: 0 <= i < |"\U{0019}a"| ==> if IsLowerCase("\U{0019}a"[i]) then IsLowerUpperPair("\U{0019}a"[i], r0[i]) else if IsUpperCase("\U{0019}a"[i]) then IsUpperLowerPair("\U{0019}a"[i], r0[i]) else r0[i] == "\U{0019}a"[i];
}
method {:test} Test58() {
var r0 := ToggleCase("2a");
expect |r0| == |"2a"|;
expect forall i :: 0 <= i < |"2a"| ==> if IsLowerCase("2a"[i]) then IsLowerUpperPair("2a"[i], r0[i]) else if IsUpperCase("2a"[i]) then IsUpperLowerPair("2a"[i], r0[i]) else r0[i] == "2a"[i];
}
method {:test} Test59() {
var r0 := ToggleCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 10 - TIME: 37.2603788 s
