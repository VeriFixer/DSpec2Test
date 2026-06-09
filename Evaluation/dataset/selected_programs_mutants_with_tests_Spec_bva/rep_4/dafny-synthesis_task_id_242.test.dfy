
method {:test} Test10() {
var r0 := CountCharacters("\U{0004}\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0\U{0002}"|;
}

// REPEAT 4 - TIME: 8.4651371 s