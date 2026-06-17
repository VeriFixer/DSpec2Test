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
    s' := s' + [ShiftMinus32(s[i])];
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
method {:test} Test1() {
var r0 := ToUppercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test3() {
var r0 := ToUppercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsLowerCase("aa"[i]) then IsLowerUpperPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 1 - TIME: 7.8012067 s

method {:test} Test10() {
var r0 := ToUppercase("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\");
expect |r0| == |"a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"|;
expect forall i :: 0 <= i < |"a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"| ==> if IsLowerCase("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i]) then IsLowerUpperPair("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i], r0[i]) else r0[i] == "a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i];
}

// REPEAT 2 - TIME: 8.7239302 s

method {:test} Test11() {
var r0 := ToUppercase("\\:8");
expect |r0| == |"\\:8"|;
expect forall i :: 0 <= i < |"\\:8"| ==> if IsLowerCase("\\:8"[i]) then IsLowerUpperPair("\\:8"[i], r0[i]) else r0[i] == "\\:8"[i];
}

// REPEAT 3 - TIME: 9.6935053 s

method {:test} Test12() {
var r0 := ToUppercase("\\a");
expect |r0| == |"\\a"|;
expect forall i :: 0 <= i < |"\\a"| ==> if IsLowerCase("\\a"[i]) then IsLowerUpperPair("\\a"[i], r0[i]) else r0[i] == "\\a"[i];
}

// REPEAT 4 - TIME: 10.5755836 s

method {:test} Test13() {
var r0 := ToUppercase(":aa");
expect |r0| == |":aa"|;
expect forall i :: 0 <= i < |":aa"| ==> if IsLowerCase(":aa"[i]) then IsLowerUpperPair(":aa"[i], r0[i]) else r0[i] == ":aa"[i];
}

// REPEAT 5 - TIME: 11.4050182 s

method {:test} Test14() {
var r0 := ToUppercase("aaTaaaa<\U{001C}");
expect |r0| == |"aaTaaaa<\U{001C}"|;
expect forall i :: 0 <= i < |"aaTaaaa<\U{001C}"| ==> if IsLowerCase("aaTaaaa<\U{001C}"[i]) then IsLowerUpperPair("aaTaaaa<\U{001C}"[i], r0[i]) else r0[i] == "aaTaaaa<\U{001C}"[i];
}

// REPEAT 6 - TIME: 12.0364129 s

method {:test} Test15() {
var r0 := ToUppercase("\U{001C}(aaaa\\aa\U{000C}");
expect |r0| == |"\U{001C}(aaaa\\aa\U{000C}"|;
expect forall i :: 0 <= i < |"\U{001C}(aaaa\\aa\U{000C}"| ==> if IsLowerCase("\U{001C}(aaaa\\aa\U{000C}"[i]) then IsLowerUpperPair("\U{001C}(aaaa\\aa\U{000C}"[i], r0[i]) else r0[i] == "\U{001C}(aaaa\\aa\U{000C}"[i];
}

// REPEAT 7 - TIME: 12.7486533 s

method {:test} Test16() {
var r0 := ToUppercase("\U{001C}\U{000C}8a");
expect |r0| == |"\U{001C}\U{000C}8a"|;
expect forall i :: 0 <= i < |"\U{001C}\U{000C}8a"| ==> if IsLowerCase("\U{001C}\U{000C}8a"[i]) then IsLowerUpperPair("\U{001C}\U{000C}8a"[i], r0[i]) else r0[i] == "\U{001C}\U{000C}8a"[i];
}

// REPEAT 8 - TIME: 13.4590072 s

method {:test} Test17() {
var r0 := ToUppercase("\U{001C}(aa<aaaa\U{0017}a");
expect |r0| == |"\U{001C}(aa<aaaa\U{0017}a"|;
expect forall i :: 0 <= i < |"\U{001C}(aa<aaaa\U{0017}a"| ==> if IsLowerCase("\U{001C}(aa<aaaa\U{0017}a"[i]) then IsLowerUpperPair("\U{001C}(aa<aaaa\U{0017}a"[i], r0[i]) else r0[i] == "\U{001C}(aa<aaaa\U{0017}a"[i];
}

// REPEAT 9 - TIME: 14.0840828 s

method {:test} Test18() {
var r0 := ToUppercase("Q\U{0004}\U{000C}a\U{001C}");
expect |r0| == |"Q\U{0004}\U{000C}a\U{001C}"|;
expect forall i :: 0 <= i < |"Q\U{0004}\U{000C}a\U{001C}"| ==> if IsLowerCase("Q\U{0004}\U{000C}a\U{001C}"[i]) then IsLowerUpperPair("Q\U{0004}\U{000C}a\U{001C}"[i], r0[i]) else r0[i] == "Q\U{0004}\U{000C}a\U{001C}"[i];
}

// REPEAT 10 - TIME: 14.845913 s
