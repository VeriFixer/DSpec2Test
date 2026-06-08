method {:testEntry} AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
    ensures |r| == |l| + 1
    ensures r[|r| - 1] == t
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
    r := l + [t];
}

method {:test} Test7() {
var int0 : (int, int) := (0,0);
var int1 : (int, int) := (0,0);
var int2 : (int, int) := (0,0);
var int3 : (int, int) := (0,0);
var int4 : (int, int) := (0,0);
var int5 : (int, int) := (0,0);
var int6 : (int, int) := (0,0);
var seqint0 : seq<(int, int)> := [int0, int1, int2, int3, int4, int5, int6];
var int7 : (int, int) := (16,17);
var r0 := AddTupleToList(seqint0, int7);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int7;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 8 - TIME: 9.7786 s
