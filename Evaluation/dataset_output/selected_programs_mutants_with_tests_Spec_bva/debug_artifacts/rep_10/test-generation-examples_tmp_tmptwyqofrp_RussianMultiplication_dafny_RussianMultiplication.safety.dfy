module RussianMultiplication {
    
    export provides mult

    method {:testEntry} mult(n0 : int, m0 : int) returns (res : int)
    ensures res == (n0 * m0);
    {
        var n, m : int;
        res := 0;
        if (n0 >= 0) {
            n,m := n0, m0;
        } 
        else {
            n,m := -n0, -m0;
        }
        while (0 < n)
        invariant (m * n + res) == (m0 * n0);
        decreases n; 
        { 
            res := res + m; 
            n := n - 1; 
        }
    }
}

method {:test} Test18() {
var r0 := RussianMultiplication.mult(7728, 109);
expect r0 == 7728 * 109;
}

// REPEAT 10 - TIME: 17.451378 s


}
