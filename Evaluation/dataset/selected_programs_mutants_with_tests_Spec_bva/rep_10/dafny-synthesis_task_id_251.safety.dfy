method {:testEntry} InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
    {
        v := [];
        for i := 0 to |s|
            invariant 0 <= i <= |s|
            invariant |v| == 2 * i
            invariant forall j :: 0 <= j < i ==> v[2*j] == x && v[2*j + 1] == s[j]
        {
            v := v + [x, s[i]];
        }
    }

method {:test} Test18() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0008}\n\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}\U{0006}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0008}\n\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}\U{0006}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 14.9113153 s
