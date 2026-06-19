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
    break;
    if IsLowerCase(s[i]) {
      s' := s' + [ShiftMinus32(s[i])];
    } else {
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

// REPEAT 1 - TIME: 7.6220472 s

method {:test} Test10() {
var r0 := ToUppercase("a`aaaaaaaaaaaaaaaaaaa\\");
expect |r0| == |"a`aaaaaaaaaaaaaaaaaaa\\"|;
expect forall i :: 0 <= i < |"a`aaaaaaaaaaaaaaaaaaa\\"| ==> if IsLowerCase("a`aaaaaaaaaaaaaaaaaaa\\"[i]) then IsLowerUpperPair("a`aaaaaaaaaaaaaaaaaaa\\"[i], r0[i]) else r0[i] == "a`aaaaaaaaaaaaaaaaaaa\\"[i];
}

// REPEAT 2 - TIME: 8.4044318 s

method {:test} Test11() {
var r0 := ToUppercase("a\U{0004}aaaaa\U{001C}");
expect |r0| == |"a\U{0004}aaaaa\U{001C}"|;
expect forall i :: 0 <= i < |"a\U{0004}aaaaa\U{001C}"| ==> if IsLowerCase("a\U{0004}aaaaa\U{001C}"[i]) then IsLowerUpperPair("a\U{0004}aaaaa\U{001C}"[i], r0[i]) else r0[i] == "a\U{0004}aaaaa\U{001C}"[i];
}

// REPEAT 3 - TIME: 9.095879 s

method {:test} Test12() {
var r0 := ToUppercase("\U{001C}(aaaaaaaaaa\\");
expect |r0| == |"\U{001C}(aaaaaaaaaa\\"|;
expect forall i :: 0 <= i < |"\U{001C}(aaaaaaaaaa\\"| ==> if IsLowerCase("\U{001C}(aaaaaaaaaa\\"[i]) then IsLowerUpperPair("\U{001C}(aaaaaaaaaa\\"[i], r0[i]) else r0[i] == "\U{001C}(aaaaaaaaaa\\"[i];
}

// REPEAT 4 - TIME: 9.9258743 s

method {:test} Test13() {
var r0 := ToUppercase("a\U{0004}aaaa\U{000C}");
expect |r0| == |"a\U{0004}aaaa\U{000C}"|;
expect forall i :: 0 <= i < |"a\U{0004}aaaa\U{000C}"| ==> if IsLowerCase("a\U{0004}aaaa\U{000C}"[i]) then IsLowerUpperPair("a\U{0004}aaaa\U{000C}"[i], r0[i]) else r0[i] == "a\U{0004}aaaa\U{000C}"[i];
}

// REPEAT 5 - TIME: 10.8004023 s

method {:test} Test14() {
var r0 := ToUppercase("<:");
expect |r0| == |"<:"|;
expect forall i :: 0 <= i < |"<:"| ==> if IsLowerCase("<:"[i]) then IsLowerUpperPair("<:"[i], r0[i]) else r0[i] == "<:"[i];
}

// REPEAT 6 - TIME: 11.5718263 s

method {:test} Test15() {
var r0 := ToUppercase("\U{000C}:a");
expect |r0| == |"\U{000C}:a"|;
expect forall i :: 0 <= i < |"\U{000C}:a"| ==> if IsLowerCase("\U{000C}:a"[i]) then IsLowerUpperPair("\U{000C}:a"[i], r0[i]) else r0[i] == "\U{000C}:a"[i];
}

// REPEAT 7 - TIME: 12.3365485 s

method {:test} Test16() {
var r0 := ToUppercase("<:aaaaaa\U{000C}aaaa\U{001C}");
expect |r0| == |"<:aaaaaa\U{000C}aaaa\U{001C}"|;
expect forall i :: 0 <= i < |"<:aaaaaa\U{000C}aaaa\U{001C}"| ==> if IsLowerCase("<:aaaaaa\U{000C}aaaa\U{001C}"[i]) then IsLowerUpperPair("<:aaaaaa\U{000C}aaaa\U{001C}"[i], r0[i]) else r0[i] == "<:aaaaaa\U{000C}aaaa\U{001C}"[i];
}

// REPEAT 8 - TIME: 13.0334156 s

method {:test} Test17() {
var r0 := ToUppercase("\U{0017}aaaaa\\\U{000C}\U{001C}");
expect |r0| == |"\U{0017}aaaaa\\\U{000C}\U{001C}"|;
expect forall i :: 0 <= i < |"\U{0017}aaaaa\\\U{000C}\U{001C}"| ==> if IsLowerCase("\U{0017}aaaaa\\\U{000C}\U{001C}"[i]) then IsLowerUpperPair("\U{0017}aaaaa\\\U{000C}\U{001C}"[i], r0[i]) else r0[i] == "\U{0017}aaaaa\\\U{000C}\U{001C}"[i];
}

// REPEAT 9 - TIME: 13.7606272 s

method {:test} Test18() {
var r0 := ToUppercase("^]aa\U{0004}aaa\U{0017}Qaa\U{000C}G9");
expect |r0| == |"^]aa\U{0004}aaa\U{0017}Qaa\U{000C}G9"|;
expect forall i :: 0 <= i < |"^]aa\U{0004}aaa\U{0017}Qaa\U{000C}G9"| ==> if IsLowerCase("^]aa\U{0004}aaa\U{0017}Qaa\U{000C}G9"[i]) then IsLowerUpperPair("^]aa\U{0004}aaa\U{0017}Qaa\U{000C}G9"[i], r0[i]) else r0[i] == "^]aa\U{0004}aaa\U{0017}Qaa\U{000C}G9"[i];
}

// REPEAT 10 - TIME: 14.5081244 s
