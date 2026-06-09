
method {:test} Test11() {
var seqint0 : seq<int> := [5, 0, 2];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 3 - TIME: 14.9193985 s