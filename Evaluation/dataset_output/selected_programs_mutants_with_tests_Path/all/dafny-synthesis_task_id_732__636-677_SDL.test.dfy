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
    if IsSpaceCommaDot(s[i]) {
      s' := s' + [':'];
    }
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

// REPEAT 1 - TIME: 27.0021864 s

method {:test} Test1() {
var r0 := ReplaceWithColon("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> (IsSpaceCommaDot("aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa"[i]) ==> r0[i] == "aa"[i]);
}

// REPEAT 2 - TIME: 103.5035457 s

method {:test} Test2() {
var r0 := ReplaceWithColon("aaa");
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> (IsSpaceCommaDot("aaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa"[i]) ==> r0[i] == "aaa"[i]);
}

// REPEAT 3 - TIME: 231.3386208 s

method {:test} Test3() {
var r0 := ReplaceWithColon("\0a \U{0001}");
expect |r0| == |"\0a \U{0001}"|;
expect forall i :: 0 <= i < |"\0a \U{0001}"| ==> (IsSpaceCommaDot("\0a \U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0a \U{0001}"[i]) ==> r0[i] == "\0a \U{0001}"[i]);
}

// REPEAT 4 - TIME: 355.5511866 s

method {:test} Test4() {
var r0 := ReplaceWithColon(" a ");
expect |r0| == |" a "|;
expect forall i :: 0 <= i < |" a "| ==> (IsSpaceCommaDot(" a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a "[i]) ==> r0[i] == " a "[i]);
}

// REPEAT 5 - TIME: 520.2351822 s

method {:test} Test5() {
var r0 := ReplaceWithColon(",aaaa");
expect |r0| == |",aaaa"|;
expect forall i :: 0 <= i < |",aaaa"| ==> (IsSpaceCommaDot(",aaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",aaaa"[i]) ==> r0[i] == ",aaaa"[i]);
}

// REPEAT 6 - TIME: 657.1853177 s

method {:test} Test6() {
var r0 := ReplaceWithColon("\0aaaaa");
expect |r0| == |"\0aaaaa"|;
expect forall i :: 0 <= i < |"\0aaaaa"| ==> (IsSpaceCommaDot("\0aaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaa"[i]) ==> r0[i] == "\0aaaaa"[i]);
}

// REPEAT 7 - TIME: 812.3902625 s

method {:test} Test7() {
var r0 := ReplaceWithColon("\0aaa");
expect |r0| == |"\0aaa"|;
expect forall i :: 0 <= i < |"\0aaa"| ==> (IsSpaceCommaDot("\0aaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaa"[i]) ==> r0[i] == "\0aaa"[i]);
}

// REPEAT 8 - TIME: 994.8255381 s

method {:test} Test8() {
var r0 := ReplaceWithColon("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (IsSpaceCommaDot(""[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(""[i]) ==> r0[i] == ""[i]);
}

// REPEAT 9 - TIME: 1134.4358174 s

method {:test} Test9() {
var r0 := ReplaceWithColon("\U{0001}aaaa\0");
expect |r0| == |"\U{0001}aaaa\0"|;
expect forall i :: 0 <= i < |"\U{0001}aaaa\0"| ==> (IsSpaceCommaDot("\U{0001}aaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0001}aaaa\0"[i]) ==> r0[i] == "\U{0001}aaaa\0"[i]);
}

// REPEAT 10 - TIME: 1289.0319822 s
