
method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [4, 0, 0, 0, 1322, 0, 0, 0, 0, 0, 0, 0];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}
method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
var r0 := InsertionSort(seqint0);
expect multiset(r0) == multiset(seqint0);
expect IsSorted(r0);
}

// REPEAT 3 - TIME: 8.4295523 s