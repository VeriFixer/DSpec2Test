
method {:test} Test10() {
var r0 := ToUppercase("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\");
expect |r0| == |"a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"|;
expect forall i :: 0 <= i < |"a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"| ==> if IsLowerCase("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i]) then IsLowerUpperPair("a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i], r0[i]) else r0[i] == "a`aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\"[i];
}

// REPEAT 2 - TIME: 7.841158 s