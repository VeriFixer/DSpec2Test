method {:testEntry} intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
{
    interspersed := [];
    for i := 0 to |numbers|
    invariant |interspersed| == if i > 0 then 2 * i - 1 else 0
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 0 ==> 
                interspersed[i0] == numbers[i0 / 2]
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 1 ==>
                interspersed[i0] == delimiter
    {
        if i > 0 {
            interspersed := interspersed + [delimiter];
        }
        interspersed := interspersed + [numbers[i]];
    }
}

method {:test} Test8() {
var seqint0 : seq<int> := [5, 0, 0, 0];
var r0 := intersperse(seqint0, 29);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 29;
}
method {:test} Test9() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7];
var r0 := intersperse(seqint0, 28);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 28;
}

// REPEAT 5 - TIME: 8.4778051 s
