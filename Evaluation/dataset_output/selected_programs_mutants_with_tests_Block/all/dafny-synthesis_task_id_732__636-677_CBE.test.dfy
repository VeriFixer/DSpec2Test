// dafny-synthesis_task_id_732.dfy

predicate IsSpaceCommaDot(c: char)
{
  c == ' ' || c == ',' || c == '.'
}

method {:testEntry} ReplaceWithColon(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> s'[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> s'[k] == s[k])
  {
    s' := s' + [s[i]];
  }
  return s';
}


predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}

method {:testEntry} ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> s'[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> s'[k] == s[k])
    {
        if IsSpaceCommaDot(s[i])
        {
            s' := s' + [':'];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test0() {
var r0 := ReplaceWithColon("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> (IsSpaceCommaDot("a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a"[i]) ==> r0[i] == "a"[i]);
}
method {:test} Test1() {
var r0 := ReplaceWithColon("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (IsSpaceCommaDot(""[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(""[i]) ==> r0[i] == ""[i]);
}
method {:test} Test3() {
var r0 := ReplaceWithColon("a\0");
expect |r0| == |"a\0"|;
expect forall i :: 0 <= i < |"a\0"| ==> (IsSpaceCommaDot("a\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0"[i]) ==> r0[i] == "a\0"[i]);
}

// REPEAT 1 - TIME: 3.742484 s

method {:test} Test4() {
var r0 := ReplaceWithColon("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> (IsSpaceCommaDot("\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0"[i]) ==> r0[i] == "\0"[i]);
}
method {:test} Test7() {
var r0 := ReplaceWithColon("a\0\U{0002}");
expect |r0| == |"a\0\U{0002}"|;
expect forall i :: 0 <= i < |"a\0\U{0002}"| ==> (IsSpaceCommaDot("a\0\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0\U{0002}"[i]) ==> r0[i] == "a\0\U{0002}"[i]);
}

// REPEAT 2 - TIME: 6.1187073 s

method {:test} Test8() {
var r0 := ReplaceWithColon(":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| == |":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> (IsSpaceCommaDot(":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]) ==> r0[i] == ":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]);
}
method {:test} Test9() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i]);
}
method {:test} Test10() {
var r0 := ReplaceWithColon("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceWithColon("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 8.6178808 s

method {:test} Test12() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a ");
expect |r0| == |"aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "| ==> (IsSpaceCommaDot("aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]) ==> r0[i] == "aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]);
}
method {:test} Test13() {
var r0 := ReplaceWithColon("\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test14() {
var r0 := ReplaceWithColon(":\0");
expect |r0| == |":\0"|;
expect forall i :: 0 <= i < |":\0"| ==> (IsSpaceCommaDot(":\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":\0"[i]) ==> r0[i] == ":\0"[i]);
}
method {:test} Test15() {
var r0 := ReplaceWithColon("a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a");
expect |r0| == |"a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"|;
expect forall i :: 0 <= i < |"a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"| ==> (IsSpaceCommaDot("a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"[i]) ==> r0[i] == "a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"[i]);
}

// REPEAT 4 - TIME: 11.41044 s

method {:test} Test16() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a ");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]);
}
method {:test} Test17() {
var r0 := ReplaceWithColon("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> (IsSpaceCommaDot("\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0"[i]) ==> r0[i] == "\0"[i]);
}
method {:test} Test18() {
var r0 := ReplaceWithColon("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 14.2016049 s

method {:test} Test20() {
var r0 := ReplaceWithColon(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  ");
expect |r0| == |" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "|;
expect forall i :: 0 <= i < |" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "| ==> (IsSpaceCommaDot(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]) ==> r0[i] == " aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]);
}
method {:test} Test21() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceWithColon("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a");
expect |r0| == |"\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"| ==> (IsSpaceCommaDot("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]) ==> r0[i] == "\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]);
}

// REPEAT 6 - TIME: 16.6608354 s

method {:test} Test24() {
var r0 := ReplaceWithColon("aaaa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaa");
expect |r0| == |"aaaa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaa"|;
expect forall i :: 0 <= i < |"aaaa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaa"| ==> (IsSpaceCommaDot("aaaa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaa"[i]) ==> r0[i] == "aaaa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaa"[i]);
}
method {:test} Test25() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test26() {
var r0 := ReplaceWithColon("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test27() {
var r0 := ReplaceWithColon("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}aa");
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}aa"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}aa"| ==> (IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}aa"[i]) ==> r0[i] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}aa"[i]);
}

// REPEAT 7 - TIME: 19.4669517 s

method {:test} Test28() {
var r0 := ReplaceWithColon("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}");
expect |r0| == |"aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"|;
expect forall i :: 0 <= i < |"aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"| ==> (IsSpaceCommaDot("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]) ==> r0[i] == "aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]);
}
method {:test} Test29() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test31() {
var r0 := ReplaceWithColon("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 8 - TIME: 22.3621363 s

method {:test} Test32() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test33() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test34() {
var r0 := ReplaceWithColon("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test35() {
var r0 := ReplaceWithColon("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a");
expect |r0| == |"a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"|;
expect forall i :: 0 <= i < |"a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"| ==> (IsSpaceCommaDot("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]) ==> r0[i] == "a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]);
}

// REPEAT 9 - TIME: 25.3294962 s

method {:test} Test36() {
var r0 := ReplaceWithColon("aaaa");
expect |r0| == |"aaaa"|;
expect forall i :: 0 <= i < |"aaaa"| ==> (IsSpaceCommaDot("aaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaa"[i]) ==> r0[i] == "aaaa"[i]);
}
method {:test} Test37() {
var r0 := ReplaceWithColon(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test38() {
var r0 := ReplaceWithColon("::");
expect |r0| == |"::"|;
expect forall i :: 0 <= i < |"::"| ==> (IsSpaceCommaDot("::"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("::"[i]) ==> r0[i] == "::"[i]);
}
method {:test} Test39() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 28.692193 s
