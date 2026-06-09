//Simple Assignment Example -- Steph Renee McIntyre
//Based on the code used in the course overheads for Fall 2018
method {:testEntry} simple(y: int) returns (x: int) 
  requires y==6;
  ensures x==7;
{
    /* (| y = 6 |)  //This is from the requires statement.*/
    
    /* (| y + 1 = 7 |) - implied (a) */ assert y+1 == 7;
    
    x := y + 1;
    
    /* (| x = 7 |) - assignment //This is from the ensures statement. */
}

/* Proof of implied (a): 
    Let y = 6.
    Then add 1 to both sides of the equality: y + 1 = 6 + 1
    Then y + 1 = 7.
*/

method {:test} Test0() {
expect 6 == 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := simple(6);
expect r0 == 7;
}

// REPEAT 1 - TIME: 3.3728923 s


// REPEAT 2 - TIME: 4.1310797 s


// REPEAT 3 - TIME: 4.8838982 s


// REPEAT 4 - TIME: 5.6259353 s


// REPEAT 5 - TIME: 6.2642137 s


// REPEAT 6 - TIME: 7.0200775 s


// REPEAT 7 - TIME: 7.7122903 s


// REPEAT 8 - TIME: 8.3483733 s


// REPEAT 9 - TIME: 9.0134973 s


// REPEAT 10 - TIME: 9.5243035 s
