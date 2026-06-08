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

// REPEAT 1 - TIME: 3.2371957 s

method {:test} Test1() {
var r0 := ReplaceWithColon("a\0");
expect |r0| == |"a\0"|;
expect forall i :: 0 <= i < |"a\0"| ==> (IsSpaceCommaDot("a\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0"[i]) ==> r0[i] == "a\0"[i]);
}

// REPEAT 2 - TIME: 4.3060293 s

method {:test} Test2() {
var r0 := ReplaceWithColon("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (IsSpaceCommaDot(""[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(""[i]) ==> r0[i] == ""[i]);
}

// REPEAT 3 - TIME: 5.284375 s

method {:test} Test3() {
var r0 := ReplaceWithColon("a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| == |"a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> (IsSpaceCommaDot("a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]) ==> r0[i] == "a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]);
}

// REPEAT 4 - TIME: 6.3628136 s

method {:test} Test4() {
var r0 := ReplaceWithColon(" a");
expect |r0| == |" a"|;
expect forall i :: 0 <= i < |" a"| ==> (IsSpaceCommaDot(" a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a"[i]) ==> r0[i] == " a"[i]);
}

// REPEAT 5 - TIME: 7.1560718 s

method {:test} Test5() {
var r0 := ReplaceWithColon(",  a");
expect |r0| == |",  a"|;
expect forall i :: 0 <= i < |",  a"| ==> (IsSpaceCommaDot(",  a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",  a"[i]) ==> r0[i] == ",  a"[i]);
}

// REPEAT 6 - TIME: 8.1077027 s

method {:test} Test6() {
var r0 := ReplaceWithColon(",  a  a");
expect |r0| == |",  a  a"|;
expect forall i :: 0 <= i < |",  a  a"| ==> (IsSpaceCommaDot(",  a  a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",  a  a"[i]) ==> r0[i] == ",  a  a"[i]);
}

// REPEAT 7 - TIME: 8.8874519 s

method {:test} Test7() {
var r0 := ReplaceWithColon(" ,a ");
expect |r0| == |" ,a "|;
expect forall i :: 0 <= i < |" ,a "| ==> (IsSpaceCommaDot(" ,a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" ,a "[i]) ==> r0[i] == " ,a "[i]);
}

// REPEAT 8 - TIME: 9.7519635 s

method {:test} Test8() {
var r0 := ReplaceWithColon("  a");
expect |r0| == |"  a"|;
expect forall i :: 0 <= i < |"  a"| ==> (IsSpaceCommaDot("  a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  a"[i]) ==> r0[i] == "  a"[i]);
}

// REPEAT 9 - TIME: 10.5647534 s

method {:test} Test9() {
var r0 := ReplaceWithColon(",  ");
expect |r0| == |",  "|;
expect forall i :: 0 <= i < |",  "| ==> (IsSpaceCommaDot(",  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",  "[i]) ==> r0[i] == ",  "[i]);
}

// REPEAT 10 - TIME: 11.2812422 s
