
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
expect 5923 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5923);
expect r0 == factorial(5923);
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(0);
expect r0 == factorial(0);
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(100);
expect r0 == factorial(100);
}
method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5);
expect r0 == factorial(5);
}
method {:test} Test7() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(1);
expect r0 == factorial(1);
}
method {:test} Test8() {
expect 5923 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5923);
expect r0 == factorial(5923);
}
method {:test} Test9() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(0);
expect r0 == factorial(0);
}
method {:test} Test10() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(100);
expect r0 == factorial(100);
}
method {:test} Test12() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5);
expect r0 == factorial(5);
}
method {:test} Test15() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(1);
expect r0 == factorial(1);
}
method {:test} Test16() {
expect 1 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(1);
expect r0 == 1 * 1;
}
method {:test} Test18() {
expect 100 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(100);
expect r0 == 100 * 100;
}
method {:test} Test20() {
expect 10 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(10);
expect r0 == 10 * 10;
}
method {:test} Test23() {
expect 1 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(1);
expect r0 == 1 * 1;
}
method {:test} Test25() {
expect 100 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(100);
expect r0 == 100 * 100;
}
method {:test} Test27() {
expect 10 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 14.3861491 s
