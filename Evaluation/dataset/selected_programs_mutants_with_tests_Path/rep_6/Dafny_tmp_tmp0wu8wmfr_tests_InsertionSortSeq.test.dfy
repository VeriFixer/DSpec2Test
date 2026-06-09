
method {:test} Test5() {
var seqint0 : seq<int> := [6, 0, 4];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 6 - TIME: 358.188222 s