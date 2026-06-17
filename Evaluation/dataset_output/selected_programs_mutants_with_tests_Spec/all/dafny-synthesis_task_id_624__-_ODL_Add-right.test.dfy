// dafny-synthesis_task_id_624.dfy

predicate IsLowerCase(c: char)
{
  97 <= c as int <= 122
}

predicate IsLowerUpperPair(c: char, C: char)
{
  c as int == C as int + 32
}

function ShiftMinus32(c: char): char
{
  ((c as int - 32) % 128) as char
}

method {:testEntry} ToUppercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) ==> s[k] == s'[k]
  {
    if IsLowerCase(s[i]) {
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

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

method {:testEntry} ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) ==> s[k] == s'[k]
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test0() {
var r0 := ToUppercase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else r0[i] == "a"[i];
}

// REPEAT 1 - TIME: 3.2346392 s

method {:test} Test1() {
var r0 := ToUppercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsLowerCase("aa"[i]) then IsLowerUpperPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 2 - TIME: 4.436779 s

method {:test} Test2() {
var r0 := ToUppercase("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\");
expect |r0| == |"a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"|;
expect forall i :: 0 <= i < |"a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"| ==> if IsLowerCase("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i]) then IsLowerUpperPair("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i], r0[i]) else r0[i] == "a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i];
}

// REPEAT 3 - TIME: 5.4392222 s

method {:test} Test3() {
var r0 := ToUppercase("\\:");
expect |r0| == |"\\:"|;
expect forall i :: 0 <= i < |"\\:"| ==> if IsLowerCase("\\:"[i]) then IsLowerUpperPair("\\:"[i], r0[i]) else r0[i] == "\\:"[i];
}

// REPEAT 4 - TIME: 6.5351084 s

method {:test} Test4() {
var r0 := ToUppercase("\U{000C}:");
expect |r0| == |"\U{000C}:"|;
expect forall i :: 0 <= i < |"\U{000C}:"| ==> if IsLowerCase("\U{000C}:"[i]) then IsLowerUpperPair("\U{000C}:"[i], r0[i]) else r0[i] == "\U{000C}:"[i];
}

// REPEAT 5 - TIME: 7.6125827 s

method {:test} Test5() {
var r0 := ToUppercase("\\:8");
expect |r0| == |"\\:8"|;
expect forall i :: 0 <= i < |"\\:8"| ==> if IsLowerCase("\\:8"[i]) then IsLowerUpperPair("\\:8"[i], r0[i]) else r0[i] == "\\:8"[i];
}

// REPEAT 6 - TIME: 8.4874865 s

method {:test} Test6() {
var r0 := ToUppercase("\U{000C}aa\\");
expect |r0| == |"\U{000C}aa\\"|;
expect forall i :: 0 <= i < |"\U{000C}aa\\"| ==> if IsLowerCase("\U{000C}aa\\"[i]) then IsLowerUpperPair("\U{000C}aa\\"[i], r0[i]) else r0[i] == "\U{000C}aa\\"[i];
}

// REPEAT 7 - TIME: 9.3194361 s

method {:test} Test7() {
var r0 := ToUppercase("]Ta");
expect |r0| == |"]Ta"|;
expect forall i :: 0 <= i < |"]Ta"| ==> if IsLowerCase("]Ta"[i]) then IsLowerUpperPair("]Ta"[i], r0[i]) else r0[i] == "]Ta"[i];
}

// REPEAT 8 - TIME: 9.9681072 s

method {:test} Test8() {
var r0 := ToUppercase("\U{0017}:");
expect |r0| == |"\U{0017}:"|;
expect forall i :: 0 <= i < |"\U{0017}:"| ==> if IsLowerCase("\U{0017}:"[i]) then IsLowerUpperPair("\U{0017}:"[i], r0[i]) else r0[i] == "\U{0017}:"[i];
}

// REPEAT 9 - TIME: 10.6837339 s

method {:test} Test9() {
var r0 := ToUppercase("\\(aaa");
expect |r0| == |"\\(aaa"|;
expect forall i :: 0 <= i < |"\\(aaa"| ==> if IsLowerCase("\\(aaa"[i]) then IsLowerUpperPair("\\(aaa"[i], r0[i]) else r0[i] == "\\(aaa"[i];
}

// REPEAT 10 - TIME: 11.3471589 s
