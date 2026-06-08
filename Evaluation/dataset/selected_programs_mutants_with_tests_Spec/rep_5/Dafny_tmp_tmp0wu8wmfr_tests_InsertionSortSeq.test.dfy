
method {:test} Test4() {
var seqint0 : seq<int> := [6, 3];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 5 - TIME: 11.8057255 s