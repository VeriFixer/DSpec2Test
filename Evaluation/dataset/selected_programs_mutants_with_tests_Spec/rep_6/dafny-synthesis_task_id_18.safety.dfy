method {:testEntry} RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{
    var v' : string := [];
    for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |v'| <= i
    invariant forall k :: 0 <= k < |v'| ==> (v'[k] in s1) && !(v'[k] in s2)
    invariant forall k :: 0 <= k < i ==> (s1[k] in s2) || (s1[k] in v')
    {
        if !(s1[i] in s2)
        {
            v' := v' + [s1[i]];
        }
    }
    return v';
}

method {:test} Test5() {
var r0 := RemoveChars("\0\0a", "\U{0002}aa");
expect |r0| <= |"\0\0a"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\0\0a" && !(r0[i] in "\U{0002}aa");
expect forall i :: 0 <= i < |"\0\0a"| ==> "\0\0a"[i] in "\U{0002}aa" || "\0\0a"[i] in r0;
}

// REPEAT 6 - TIME: 7.6650649 s
