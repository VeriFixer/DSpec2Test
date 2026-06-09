method {:testEntry} ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> s'[k] == ch) && (s[k] != ' ' ==> s'[k] == s[k])
    {
        if s[i] == ' '
        {
            s' := s' + [ch];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa", '\0');
expect |r0| == |"\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"|;
expect forall i :: 0 <= i < |"\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"| ==> ("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i] != ' ' ==> r0[i] == "\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i]);
}
method {:test} Test14() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa", '\0');
expect |r0| == |"aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"| ==> ("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i]);
}

// REPEAT 5 - TIME: 9.1519547 s
