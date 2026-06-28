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
    } else {
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

// REPEAT 1 - TIME: 6.479792 s

method {:test} Test6() {
var r0 := ToggleCase("@");
expect |r0| == |"@"|;
expect forall i :: 0 <= i < |"@"| ==> if IsLowerCase("@"[i]) then IsLowerUpperPair("@"[i], r0[i]) else if IsUpperCase("@"[i]) then IsUpperLowerPair("@"[i], r0[i]) else r0[i] == "@"[i];
}
method {:test} Test7() {
var r0 := ToggleCase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test9() {
var r0 := ToggleCase("K");
expect |r0| == |"K"|;
expect forall i :: 0 <= i < |"K"| ==> if IsLowerCase("K"[i]) then IsLowerUpperPair("K"[i], r0[i]) else if IsUpperCase("K"[i]) then IsUpperLowerPair("K"[i], r0[i]) else r0[i] == "K"[i];
}
method {:test} Test11() {
var r0 := ToggleCase("{");
expect |r0| == |"{"|;
expect forall i :: 0 <= i < |"{"| ==> if IsLowerCase("{"[i]) then IsLowerUpperPair("{"[i], r0[i]) else if IsUpperCase("{"[i]) then IsUpperLowerPair("{"[i], r0[i]) else r0[i] == "{"[i];
}

// REPEAT 2 - TIME: 10.1492656 s

method {:test} Test12() {
var r0 := ToggleCase("c");
expect |r0| == |"c"|;
expect forall i :: 0 <= i < |"c"| ==> if IsLowerCase("c"[i]) then IsLowerUpperPair("c"[i], r0[i]) else if IsUpperCase("c"[i]) then IsUpperLowerPair("c"[i], r0[i]) else r0[i] == "c"[i];
}
method {:test} Test13() {
var r0 := ToggleCase("aaa");
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> if IsLowerCase("aaa"[i]) then IsLowerUpperPair("aaa"[i], r0[i]) else if IsUpperCase("aaa"[i]) then IsUpperLowerPair("aaa"[i], r0[i]) else r0[i] == "aaa"[i];
}
method {:test} Test14() {
var r0 := ToggleCase("aaaaaaaaaaxaaaass");
expect |r0| == |"aaaaaaaaaaxaaaass"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaxaaaass"| ==> if IsLowerCase("aaaaaaaaaaxaaaass"[i]) then IsLowerUpperPair("aaaaaaaaaaxaaaass"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaxaaaass"[i]) then IsUpperLowerPair("aaaaaaaaaaxaaaass"[i], r0[i]) else r0[i] == "aaaaaaaaaaxaaaass"[i];
}
method {:test} Test15() {
var r0 := ToggleCase(">=+");
expect |r0| == |">=+"|;
expect forall i :: 0 <= i < |">=+"| ==> if IsLowerCase(">=+"[i]) then IsLowerUpperPair(">=+"[i], r0[i]) else if IsUpperCase(">=+"[i]) then IsUpperLowerPair(">=+"[i], r0[i]) else r0[i] == ">=+"[i];
}
method {:test} Test16() {
var r0 := ToggleCase("ba");
expect |r0| == |"ba"|;
expect forall i :: 0 <= i < |"ba"| ==> if IsLowerCase("ba"[i]) then IsLowerUpperPair("ba"[i], r0[i]) else if IsUpperCase("ba"[i]) then IsUpperLowerPair("ba"[i], r0[i]) else r0[i] == "ba"[i];
}
method {:test} Test17() {
var r0 := ToggleCase("a:a");
expect |r0| == |"a:a"|;
expect forall i :: 0 <= i < |"a:a"| ==> if IsLowerCase("a:a"[i]) then IsLowerUpperPair("a:a"[i], r0[i]) else if IsUpperCase("a:a"[i]) then IsUpperLowerPair("a:a"[i], r0[i]) else r0[i] == "a:a"[i];
}

// REPEAT 3 - TIME: 13.2672454 s

method {:test} Test18() {
var r0 := ToggleCase("gaawaaaabafaaaaaae");
expect |r0| == |"gaawaaaabafaaaaaae"|;
expect forall i :: 0 <= i < |"gaawaaaabafaaaaaae"| ==> if IsLowerCase("gaawaaaabafaaaaaae"[i]) then IsLowerUpperPair("gaawaaaabafaaaaaae"[i], r0[i]) else if IsUpperCase("gaawaaaabafaaaaaae"[i]) then IsUpperLowerPair("gaawaaaabafaaaaaae"[i], r0[i]) else r0[i] == "gaawaaaabafaaaaaae"[i];
}
method {:test} Test19() {
var r0 := ToggleCase("\U{0003}a\U{0002}a");
expect |r0| == |"\U{0003}a\U{0002}a"|;
expect forall i :: 0 <= i < |"\U{0003}a\U{0002}a"| ==> if IsLowerCase("\U{0003}a\U{0002}a"[i]) then IsLowerUpperPair("\U{0003}a\U{0002}a"[i], r0[i]) else if IsUpperCase("\U{0003}a\U{0002}a"[i]) then IsUpperLowerPair("\U{0003}a\U{0002}a"[i], r0[i]) else r0[i] == "\U{0003}a\U{0002}a"[i];
}
method {:test} Test20() {
var r0 := ToggleCase("\U{0018}2\U{000E}");
expect |r0| == |"\U{0018}2\U{000E}"|;
expect forall i :: 0 <= i < |"\U{0018}2\U{000E}"| ==> if IsLowerCase("\U{0018}2\U{000E}"[i]) then IsLowerUpperPair("\U{0018}2\U{000E}"[i], r0[i]) else if IsUpperCase("\U{0018}2\U{000E}"[i]) then IsUpperLowerPair("\U{0018}2\U{000E}"[i], r0[i]) else r0[i] == "\U{0018}2\U{000E}"[i];
}
method {:test} Test21() {
var r0 := ToggleCase("a7aaaaaaaaaaaaaaaa");
expect |r0| == |"a7aaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"a7aaaaaaaaaaaaaaaa"| ==> if IsLowerCase("a7aaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("a7aaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("a7aaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("a7aaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "a7aaaaaaaaaaaaaaaa"[i];
}
method {:test} Test22() {
var r0 := ToggleCase("\'asaaaaaaaaaaaaaaa");
expect |r0| == |"\'asaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\'asaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\'asaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\'asaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\'asaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\'asaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\'asaaaaaaaaaaaaaaa"[i];
}
method {:test} Test23() {
var r0 := ToggleCase("a\U{0004}\U{0001}aaaaaaaaaaaaaag");
expect |r0| == |"a\U{0004}\U{0001}aaaaaaaaaaaaaag"|;
expect forall i :: 0 <= i < |"a\U{0004}\U{0001}aaaaaaaaaaaaaag"| ==> if IsLowerCase("a\U{0004}\U{0001}aaaaaaaaaaaaaag"[i]) then IsLowerUpperPair("a\U{0004}\U{0001}aaaaaaaaaaaaaag"[i], r0[i]) else if IsUpperCase("a\U{0004}\U{0001}aaaaaaaaaaaaaag"[i]) then IsUpperLowerPair("a\U{0004}\U{0001}aaaaaaaaaaaaaag"[i], r0[i]) else r0[i] == "a\U{0004}\U{0001}aaaaaaaaaaaaaag"[i];
}

// REPEAT 4 - TIME: 16.6899947 s

method {:test} Test24() {
var r0 := ToggleCase("aaaaaaaaaaaaaaacaaayag");
expect |r0| == |"aaaaaaaaaaaaaaacaaayag"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaacaaayag"| ==> if IsLowerCase("aaaaaaaaaaaaaaacaaayag"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaacaaayag"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaacaaayag"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaacaaayag"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaacaaayag"[i];
}
method {:test} Test25() {
var r0 := ToggleCase(">aaaa");
expect |r0| == |">aaaa"|;
expect forall i :: 0 <= i < |">aaaa"| ==> if IsLowerCase(">aaaa"[i]) then IsLowerUpperPair(">aaaa"[i], r0[i]) else if IsUpperCase(">aaaa"[i]) then IsUpperLowerPair(">aaaa"[i], r0[i]) else r0[i] == ">aaaa"[i];
}
method {:test} Test26() {
var r0 := ToggleCase("\U{0017}raaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0017}raaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0017}raaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0017}raaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0017}raaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{0017}raaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0017}raaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0017}raaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test27() {
var r0 := ToggleCase("aaaaa");
expect |r0| == |"aaaaa"|;
expect forall i :: 0 <= i < |"aaaaa"| ==> if IsLowerCase("aaaaa"[i]) then IsLowerUpperPair("aaaaa"[i], r0[i]) else if IsUpperCase("aaaaa"[i]) then IsUpperLowerPair("aaaaa"[i], r0[i]) else r0[i] == "aaaaa"[i];
}
method {:test} Test28() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test29() {
var r0 := ToggleCase("aa$aaaaa\0aaaaa\U{0003}aaa\U{0005}");
expect |r0| == |"aa$aaaaa\0aaaaa\U{0003}aaa\U{0005}"|;
expect forall i :: 0 <= i < |"aa$aaaaa\0aaaaa\U{0003}aaa\U{0005}"| ==> if IsLowerCase("aa$aaaaa\0aaaaa\U{0003}aaa\U{0005}"[i]) then IsLowerUpperPair("aa$aaaaa\0aaaaa\U{0003}aaa\U{0005}"[i], r0[i]) else if IsUpperCase("aa$aaaaa\0aaaaa\U{0003}aaa\U{0005}"[i]) then IsUpperLowerPair("aa$aaaaa\0aaaaa\U{0003}aaa\U{0005}"[i], r0[i]) else r0[i] == "aa$aaaaa\0aaaaa\U{0003}aaa\U{0005}"[i];
}

// REPEAT 5 - TIME: 20.1804441 s

method {:test} Test30() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaag");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaag"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaag"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaag"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaag"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaag"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaag"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaag"[i];
}
method {:test} Test31() {
var r0 := ToggleCase("0a");
expect |r0| == |"0a"|;
expect forall i :: 0 <= i < |"0a"| ==> if IsLowerCase("0a"[i]) then IsLowerUpperPair("0a"[i], r0[i]) else if IsUpperCase("0a"[i]) then IsUpperLowerPair("0a"[i], r0[i]) else r0[i] == "0a"[i];
}
method {:test} Test32() {
var r0 := ToggleCase("\U{0017}aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0017}aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0017}aaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0017}aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0017}aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{0017}aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0017}aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0017}aaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test33() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test34() {
var r0 := ToggleCase("(a");
expect |r0| == |"(a"|;
expect forall i :: 0 <= i < |"(a"| ==> if IsLowerCase("(a"[i]) then IsLowerUpperPair("(a"[i], r0[i]) else if IsUpperCase("(a"[i]) then IsUpperLowerPair("(a"[i], r0[i]) else r0[i] == "(a"[i];
}
method {:test} Test35() {
var r0 := ToggleCase("(aaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}a");
expect |r0| == |"(aaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}a"|;
expect forall i :: 0 <= i < |"(aaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}a"| ==> if IsLowerCase("(aaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}a"[i]) then IsLowerUpperPair("(aaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}a"[i], r0[i]) else if IsUpperCase("(aaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}a"[i]) then IsUpperLowerPair("(aaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}a"[i], r0[i]) else r0[i] == "(aaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}a"[i];
}

// REPEAT 6 - TIME: 23.6639283 s

method {:test} Test36() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test38() {
var r0 := ToggleCase(")a");
expect |r0| == |")a"|;
expect forall i :: 0 <= i < |")a"| ==> if IsLowerCase(")a"[i]) then IsLowerUpperPair(")a"[i], r0[i]) else if IsUpperCase(")a"[i]) then IsUpperLowerPair(")a"[i], r0[i]) else r0[i] == ")a"[i];
}
method {:test} Test41() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaTaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaTaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaTaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaTaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaTaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaTaaaaaaaaaaaaa"[i];
}

// REPEAT 7 - TIME: 28.0567389 s

method {:test} Test42() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test47() {
var r0 := ToggleCase("aaDaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaDaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaDaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaDaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaDaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaDaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaDaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaDaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 8 - TIME: 31.1931545 s

method {:test} Test48() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test49() {
var r0 := ToggleCase("\U{000E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{000E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{000E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{000E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{000E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{000E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{000E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{000E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test50() {
var r0 := ToggleCase("\U{001E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{001E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{001E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{001E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{001E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{001E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{001E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{001E}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test51() {
var r0 := ToggleCase("Waaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Waaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Waaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Waaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Waaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("Waaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("Waaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Waaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test52() {
var r0 := ToggleCase("\U{0019}a");
expect |r0| == |"\U{0019}a"|;
expect forall i :: 0 <= i < |"\U{0019}a"| ==> if IsLowerCase("\U{0019}a"[i]) then IsLowerUpperPair("\U{0019}a"[i], r0[i]) else if IsUpperCase("\U{0019}a"[i]) then IsUpperLowerPair("\U{0019}a"[i], r0[i]) else r0[i] == "\U{0019}a"[i];
}
method {:test} Test53() {
var r0 := ToggleCase("\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa");
expect |r0| == |"\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"|;
expect forall i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"| ==> if IsLowerCase("\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i]) then IsLowerUpperPair("\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i], r0[i]) else if IsUpperCase("\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i]) then IsUpperLowerPair("\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i], r0[i]) else r0[i] == "\U{0004}aaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i];
}

// REPEAT 9 - TIME: 35.1600114 s

method {:test} Test54() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test55() {
var r0 := ToggleCase("wa");
expect |r0| == |"wa"|;
expect forall i :: 0 <= i < |"wa"| ==> if IsLowerCase("wa"[i]) then IsLowerUpperPair("wa"[i], r0[i]) else if IsUpperCase("wa"[i]) then IsUpperLowerPair("wa"[i], r0[i]) else r0[i] == "wa"[i];
}
method {:test} Test56() {
var r0 := ToggleCase("ea");
expect |r0| == |"ea"|;
expect forall i :: 0 <= i < |"ea"| ==> if IsLowerCase("ea"[i]) then IsLowerUpperPair("ea"[i], r0[i]) else if IsUpperCase("ea"[i]) then IsUpperLowerPair("ea"[i], r0[i]) else r0[i] == "ea"[i];
}
method {:test} Test57() {
var r0 := ToggleCase("Qa");
expect |r0| == |"Qa"|;
expect forall i :: 0 <= i < |"Qa"| ==> if IsLowerCase("Qa"[i]) then IsLowerUpperPair("Qa"[i], r0[i]) else if IsUpperCase("Qa"[i]) then IsUpperLowerPair("Qa"[i], r0[i]) else r0[i] == "Qa"[i];
}
method {:test} Test58() {
var r0 := ToggleCase("qa");
expect |r0| == |"qa"|;
expect forall i :: 0 <= i < |"qa"| ==> if IsLowerCase("qa"[i]) then IsLowerUpperPair("qa"[i], r0[i]) else if IsUpperCase("qa"[i]) then IsUpperLowerPair("qa"[i], r0[i]) else r0[i] == "qa"[i];
}
method {:test} Test59() {
var r0 := ToggleCase("aaaaaaaaaaaaaDaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaDaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaDaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaDaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaDaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaDaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaDaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaDaaaaaaaaaaaa"[i];
}

// REPEAT 10 - TIME: 40.0905088 s
