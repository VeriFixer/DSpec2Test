
method {:test} Test3() {
var seqint0 : seq<int> := [2, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 4 - TIME: 182.9550884 s