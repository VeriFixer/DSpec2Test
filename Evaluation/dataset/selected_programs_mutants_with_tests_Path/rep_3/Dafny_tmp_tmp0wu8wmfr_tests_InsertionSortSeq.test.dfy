
method {:test} Test2() {
var seqint0 : seq<int> := [1];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 3 - TIME: 115.4778992 s