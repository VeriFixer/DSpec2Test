method {:testEntry} Swap(a: int, b: int) returns (result: seq<int>)
    ensures |result| == 2
    ensures result[0] == b
    ensures result[1] == a
{
    result := [b, a];
}

method {:test} Test16() {
var r0 := Swap(43, 42);
expect |r0| == 2;
expect r0[0] == 42;
expect r0[1] == 43;
}

// REPEAT 10 - TIME: 12.9627821 s
