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

// REPEAT 1 - TIME: 2.441259 s


// REPEAT 2 - TIME: 3.2320605 s


// REPEAT 3 - TIME: 3.8124142 s


// REPEAT 4 - TIME: 4.4259873 s


// REPEAT 5 - TIME: 5.0577488 s


// REPEAT 6 - TIME: 5.680661 s


// REPEAT 7 - TIME: 6.2908492 s


// REPEAT 8 - TIME: 6.794916 s


// REPEAT 9 - TIME: 7.3421807 s


// REPEAT 10 - TIME: 7.8935716 s
