
method {:testEntry} multipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures less < x < more


method {:testEntry} multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more + less == 2*x

// TODO: Hacer en casa
method {:testEntry} multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more - less == 2*y

function factorial(n:int):int
requires n>=0
{
    if n==0 || n==1 then 1 else n*factorial(n-1)
}

// PROGRAMA VERIFICADOR DE WHILE
method {:testEntry} ComputeFact (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)

{   
    assert 0 <= n <= n && 1*factorial(n) == factorial(n);
    f:=1;
    assert 0 <= n <= n && f*factorial(n) == factorial(n);
    var x:=n;
    assert 0 <= x <= n && f*factorial(x) == factorial(n);
    while x > 0 
        invariant 0 <= x <= n;
        invariant f*factorial(x)== factorial(n);
        decreases x-0;
    {
        assert 0 <= x-1 <= n && (f*x)*factorial(x-1) == factorial(n);
        f:= f*x;
        assert 0 <= x-1 <= n && f*factorial(x-1) == factorial(n);
        x:=x-1;
        assert 0 <= x <= n && f*factorial(x) == factorial(n);
    }
    assert 0 <= x <= n && f*factorial(x) == factorial(n);
}

method {:testEntry} ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
    var x:= 0;
    f:= 1;
    while x<n
        invariant 0<=x<=n;
        invariant f==factorial(x);
        decreases n - x;
    {
        x:=x+1;
        f:= f*x;
        assert 0<=x<=n && f==factorial(x);  
    }
    
}


// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n

method {:testEntry} Sqare(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    assert 1==1 && 1 <= 1 <= a;
    var y:=1;
    assert y*y==1 && 1 <= y <= a;
    x:=1;
    while y < a 
        invariant 1 <= y <= a;
        invariant y*y==x;
    {
        assert (y+1)*(y+1)==x+ (2*(y+1)-1) && 1 <= (y+1) <= a;
        y:= y+1;
        assert y*y==x+ (2*y-1) && 1 <= y <= a;
        x:= x+ (2*y-1);
        assert y*y==x && 1 <= y <= a;
    }
    assert y*y==x && 1 <= y <= a;
}


function sumSerie(n:int):int
requires n >=1 
{
    if n==1 then 1 else sumSerie(n-1) + 2*n -1
}

lemma {:induction false} Sqare_Lemma (n:int)
requires n>=1
ensures sumSerie(n) == n*n
{
    if n==1 {}
    else{
        Sqare_Lemma(n-1);
        assert sumSerie(n-1) ==(n-1)*(n-1);

        calc == {
            sumSerie(n);
            sumSerie(n-1) + 2*n -1;
            {
                Sqare_Lemma(n-1);
                assert sumSerie(n-1) ==(n-1)*(n-1);
            }
            (n-1)*(n-1) + 2*n -1;
            n*n-2*n+1 +2*n -1;
            n*n;
        }
    assert sumSerie(n) == n*n;
    }
}


method {:testEntry} Sqare2(a:int) returns (x:int)
requires a>=1
ensures x == a*a

{
    assert 1 <= 1 <= a && 1==1*1;
    var y:=1;
    assert 1 <= y <= a && 1==y*y;
    x:=1;
    assert 1 <= y <= a && x==y*y;
    while y < a 
        invariant 1 <= y <= a
        invariant x==y*y
        decreases a - y
    {
        assert 1 <= (y+1) <= a && (x+2*(y+1)-1)==(y+1)*(y+1);
        y:= y+1;
        assert 1 <= y <= a && (x+2*y-1)==y*y;
        x:= x +2*y -1;
        assert 1 <= y <= a && x==y*y;
    }
    assert 1 <= y <= a && x==y*y;
}

method {:test} Test0() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(3);
expect r0 == factorial(3);
}
method {:test} Test1() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(4);
expect r0 == factorial(4);
}
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(2);
expect r0 == factorial(2);
}
method {:test} Test3() {
expect 1 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(1);
expect r0 == 1 * 1;
}
method {:test} Test4() {
expect 2 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(2);
expect r0 == 2 * 2;
}
method {:test} Test5() {
expect 39 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(39);
expect r0 == 39 * 39;
}
method {:test} Test6() {
expect 2 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(2);
expect r0 == 2 * 2;
}

// REPEAT 1 - TIME: 6.138241 s

method {:test} Test7() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5);
expect r0 == factorial(5);
}
method {:test} Test9() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(3);
expect r0 == factorial(3);
}
method {:test} Test10() {
expect 3 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(3);
expect r0 == 3 * 3;
}
method {:test} Test12() {
expect 40 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(40);
expect r0 == 40 * 40;
}

// REPEAT 2 - TIME: 9.5840761 s

method {:test} Test14() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(6);
expect r0 == factorial(6);
}
method {:test} Test16() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(4);
expect r0 == factorial(4);
}
method {:test} Test17() {
expect 4 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(4);
expect r0 == 4 * 4;
}
method {:test} Test19() {
expect 41 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(41);
expect r0 == 41 * 41;
}

// REPEAT 3 - TIME: 12.8341956 s

method {:test} Test21() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(7);
expect r0 == factorial(7);
}
method {:test} Test23() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5);
expect r0 == factorial(5);
}
method {:test} Test24() {
expect 5 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(5);
expect r0 == 5 * 5;
}
method {:test} Test26() {
expect 42 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(42);
expect r0 == 42 * 42;
}

// REPEAT 4 - TIME: 15.8522834 s

method {:test} Test28() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(8);
expect r0 == factorial(8);
}
method {:test} Test29() {
expect 2006 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(2006);
expect r0 == factorial(2006);
}
method {:test} Test30() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(6);
expect r0 == factorial(6);
}
method {:test} Test31() {
expect 6 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(6);
expect r0 == 6 * 6;
}
method {:test} Test33() {
expect 43 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(43);
expect r0 == 43 * 43;
}

// REPEAT 5 - TIME: 18.4773481 s

method {:test} Test35() {
expect 2007 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(2007);
expect r0 == factorial(2007);
}
method {:test} Test37() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(7);
expect r0 == factorial(7);
}
method {:test} Test38() {
expect 7 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(7);
expect r0 == 7 * 7;
}
method {:test} Test40() {
expect 44 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(44);
expect r0 == 44 * 44;
}

// REPEAT 6 - TIME: 21.1738675 s

method {:test} Test42() {
expect 2008 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(2008);
expect r0 == factorial(2008);
}
method {:test} Test44() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(8);
expect r0 == factorial(8);
}
method {:test} Test45() {
expect 8 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(8);
expect r0 == 8 * 8;
}
method {:test} Test47() {
expect 45 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(45);
expect r0 == 45 * 45;
}

// REPEAT 7 - TIME: 24.4939913 s

method {:test} Test49() {
expect 2009 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(2009);
expect r0 == factorial(2009);
}
method {:test} Test51() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(9);
expect r0 == factorial(9);
}
method {:test} Test52() {
expect 9 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(9);
expect r0 == 9 * 9;
}
method {:test} Test54() {
expect 46 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(46);
expect r0 == 46 * 46;
}

// REPEAT 8 - TIME: 28.2073118 s

method {:test} Test56() {
expect 2010 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(2010);
expect r0 == factorial(2010);
}
method {:test} Test58() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(10);
expect r0 == factorial(10);
}
method {:test} Test59() {
expect 10 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(10);
expect r0 == 10 * 10;
}
method {:test} Test61() {
expect 47 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(47);
expect r0 == 47 * 47;
}

// REPEAT 9 - TIME: 30.9404965 s

method {:test} Test63() {
expect 2011 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(2011);
expect r0 == factorial(2011);
}
method {:test} Test65() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(11);
expect r0 == factorial(11);
}
method {:test} Test66() {
expect 11 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(11);
expect r0 == 11 * 11;
}
method {:test} Test68() {
expect 48 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(48);
expect r0 == 48 * 48;
}

// REPEAT 10 - TIME: 33.51944 s
