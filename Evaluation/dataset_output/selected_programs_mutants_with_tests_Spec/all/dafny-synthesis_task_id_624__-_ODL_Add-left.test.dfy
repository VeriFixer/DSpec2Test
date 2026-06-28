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
      s' := [ShiftMinus32(s[i])];
    } else {
      s' := [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ToUppercase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else r0[i] == "a"[i];
}

// REPEAT 1 - TIME: 3.2162979 s

method {:test} Test1() {
var r0 := ToUppercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsLowerCase("aa"[i]) then IsLowerUpperPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 2 - TIME: 4.1993899 s

method {:test} Test2() {
var r0 := ToUppercase("a`aaaaaaaaaaaaaaaaaaa\\");
expect |r0| == |"a`aaaaaaaaaaaaaaaaaaa\\"|;
expect forall i :: 0 <= i < |"a`aaaaaaaaaaaaaaaaaaa\\"| ==> if IsLowerCase("a`aaaaaaaaaaaaaaaaaaa\\"[i]) then IsLowerUpperPair("a`aaaaaaaaaaaaaaaaaaa\\"[i], r0[i]) else r0[i] == "a`aaaaaaaaaaaaaaaaaaa\\"[i];
}

// REPEAT 3 - TIME: 5.4879582 s

method {:test} Test3() {
var r0 := ToUppercase("\\8a");
expect |r0| == |"\\8a"|;
expect forall i :: 0 <= i < |"\\8a"| ==> if IsLowerCase("\\8a"[i]) then IsLowerUpperPair("\\8a"[i], r0[i]) else r0[i] == "\\8a"[i];
}

// REPEAT 4 - TIME: 6.8649631 s

method {:test} Test4() {
var r0 := ToUppercase("a\U{0004}aaaaaaaaaaaaaaaaaaaa\U{000C}");
expect |r0| == |"a\U{0004}aaaaaaaaaaaaaaaaaaaa\U{000C}"|;
expect forall i :: 0 <= i < |"a\U{0004}aaaaaaaaaaaaaaaaaaaa\U{000C}"| ==> if IsLowerCase("a\U{0004}aaaaaaaaaaaaaaaaaaaa\U{000C}"[i]) then IsLowerUpperPair("a\U{0004}aaaaaaaaaaaaaaaaaaaa\U{000C}"[i], r0[i]) else r0[i] == "a\U{0004}aaaaaaaaaaaaaaaaaaaa\U{000C}"[i];
}

// REPEAT 5 - TIME: 8.084487 s

method {:test} Test5() {
var r0 := ToUppercase("\U{000C}(aaa\\");
expect |r0| == |"\U{000C}(aaa\\"|;
expect forall i :: 0 <= i < |"\U{000C}(aaa\\"| ==> if IsLowerCase("\U{000C}(aaa\\"[i]) then IsLowerUpperPair("\U{000C}(aaa\\"[i], r0[i]) else r0[i] == "\U{000C}(aaa\\"[i];
}

// REPEAT 6 - TIME: 9.2929941 s

method {:test} Test6() {
var r0 := ToUppercase("\\(aaaa\U{001C}aaaaaaaaaaaaa\U{000C}a<\U{0017}");
expect |r0| == |"\\(aaaa\U{001C}aaaaaaaaaaaaa\U{000C}a<\U{0017}"|;
expect forall i :: 0 <= i < |"\\(aaaa\U{001C}aaaaaaaaaaaaa\U{000C}a<\U{0017}"| ==> if IsLowerCase("\\(aaaa\U{001C}aaaaaaaaaaaaa\U{000C}a<\U{0017}"[i]) then IsLowerUpperPair("\\(aaaa\U{001C}aaaaaaaaaaaaa\U{000C}a<\U{0017}"[i], r0[i]) else r0[i] == "\\(aaaa\U{001C}aaaaaaaaaaaaa\U{000C}a<\U{0017}"[i];
}

// REPEAT 7 - TIME: 10.2444583 s

method {:test} Test7() {
var r0 := ToUppercase("a\U{0004}aaaa\U{001C}aaaaaaaaaaaaaaa<\U{0017}a");
expect |r0| == |"a\U{0004}aaaa\U{001C}aaaaaaaaaaaaaaa<\U{0017}a"|;
expect forall i :: 0 <= i < |"a\U{0004}aaaa\U{001C}aaaaaaaaaaaaaaa<\U{0017}a"| ==> if IsLowerCase("a\U{0004}aaaa\U{001C}aaaaaaaaaaaaaaa<\U{0017}a"[i]) then IsLowerUpperPair("a\U{0004}aaaa\U{001C}aaaaaaaaaaaaaaa<\U{0017}a"[i], r0[i]) else r0[i] == "a\U{0004}aaaa\U{001C}aaaaaaaaaaaaaaa<\U{0017}a"[i];
}

// REPEAT 8 - TIME: 11.2588071 s

method {:test} Test8() {
var r0 := ToUppercase("\U{001C}(aaa\U{000C}");
expect |r0| == |"\U{001C}(aaa\U{000C}"|;
expect forall i :: 0 <= i < |"\U{001C}(aaa\U{000C}"| ==> if IsLowerCase("\U{001C}(aaa\U{000C}"[i]) then IsLowerUpperPair("\U{001C}(aaa\U{000C}"[i], r0[i]) else r0[i] == "\U{001C}(aaa\U{000C}"[i];
}

// REPEAT 9 - TIME: 12.0832886 s

method {:test} Test9() {
var r0 := ToUppercase("\U{000F}aaaaa9aaaaaaaaaaaGaaaa!aa");
expect |r0| == |"\U{000F}aaaaa9aaaaaaaaaaaGaaaa!aa"|;
expect forall i :: 0 <= i < |"\U{000F}aaaaa9aaaaaaaaaaaGaaaa!aa"| ==> if IsLowerCase("\U{000F}aaaaa9aaaaaaaaaaaGaaaa!aa"[i]) then IsLowerUpperPair("\U{000F}aaaaa9aaaaaaaaaaaGaaaa!aa"[i], r0[i]) else r0[i] == "\U{000F}aaaaa9aaaaaaaaaaaGaaaa!aa"[i];
}

// REPEAT 10 - TIME: 12.9988318 s
