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
var r0 := ReplaceWithColon("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> (IsSpaceCommaDot("aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa"[i]) ==> r0[i] == "aa"[i]);
}

// REPEAT 1 - TIME: 5.8898931 s

method {:test} Test10() {
var r0 := ReplaceWithColon("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 6.7643098 s

method {:test} Test11() {
var r0 := ReplaceWithColon(" a ");
expect |r0| == |" a "|;
expect forall i :: 0 <= i < |" a "| ==> (IsSpaceCommaDot(" a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a "[i]) ==> r0[i] == " a "[i]);
}

// REPEAT 3 - TIME: 7.5886568 s

method {:test} Test12() {
var r0 := ReplaceWithColon("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa ");
expect |r0| == |"aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "| ==> (IsSpaceCommaDot("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]) ==> r0[i] == "aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]);
}

// REPEAT 4 - TIME: 8.3197189 s

method {:test} Test13() {
var r0 := ReplaceWithColon("aaaa ");
expect |r0| == |"aaaa "|;
expect forall i :: 0 <= i < |"aaaa "| ==> (IsSpaceCommaDot("aaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaa "[i]) ==> r0[i] == "aaaa "[i]);
}

// REPEAT 5 - TIME: 8.9764454 s

method {:test} Test14() {
var r0 := ReplaceWithColon(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa ");
expect |r0| == |" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "|;
expect forall i :: 0 <= i < |" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "| ==> (IsSpaceCommaDot(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]) ==> r0[i] == " aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]);
}

// REPEAT 6 - TIME: 9.779965 s

method {:test} Test15() {
var r0 := ReplaceWithColon(" a aa ");
expect |r0| == |" a aa "|;
expect forall i :: 0 <= i < |" a aa "| ==> (IsSpaceCommaDot(" a aa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a aa "[i]) ==> r0[i] == " a aa "[i]);
}

// REPEAT 7 - TIME: 10.3299248 s

method {:test} Test16() {
var r0 := ReplaceWithColon("  aa   a");
expect |r0| == |"  aa   a"|;
expect forall i :: 0 <= i < |"  aa   a"| ==> (IsSpaceCommaDot("  aa   a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  aa   a"[i]) ==> r0[i] == "  aa   a"[i]);
}

// REPEAT 8 - TIME: 10.9776562 s

method {:test} Test17() {
var r0 := ReplaceWithColon("\U{0003}aaaa\0\U{0001}a\U{0002}");
expect |r0| == |"\U{0003}aaaa\0\U{0001}a\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0003}aaaa\0\U{0001}a\U{0002}"| ==> (IsSpaceCommaDot("\U{0003}aaaa\0\U{0001}a\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0003}aaaa\0\U{0001}a\U{0002}"[i]) ==> r0[i] == "\U{0003}aaaa\0\U{0001}a\U{0002}"[i]);
}

// REPEAT 9 - TIME: 11.6338965 s

method {:test} Test18() {
var r0 := ReplaceWithColon("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa");
expect |r0| == |"\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"|;
expect forall i :: 0 <= i < |"\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"| ==> (IsSpaceCommaDot("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]) ==> r0[i] == "\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]);
}

// REPEAT 10 - TIME: 12.2204044 s
