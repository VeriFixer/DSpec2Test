
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
expect 5923 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5923);
expect r0 == factorial(5923);
}
method {:test} Test2() {
expect 1 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(1);
expect r0 == 1 * 1;
}
method {:test} Test3() {
expect 1 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(1);
expect r0 == 1 * 1;
}

// REPEAT 1 - TIME: 4.9758574 s

method {:test} Test4() {
expect 5924 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5924);
expect r0 == factorial(5924);
}
method {:test} Test5() {
expect 5924 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5924);
expect r0 == factorial(5924);
}
method {:test} Test6() {
expect 2 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(2);
expect r0 == 2 * 2;
}
method {:test} Test7() {
expect 2 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(2);
expect r0 == 2 * 2;
}

// REPEAT 2 - TIME: 7.7467397 s

method {:test} Test8() {
expect 5925 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5925);
expect r0 == factorial(5925);
}
method {:test} Test9() {
expect 5925 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5925);
expect r0 == factorial(5925);
}
method {:test} Test10() {
expect 3 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(3);
expect r0 == 3 * 3;
}
method {:test} Test11() {
expect 3 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(3);
expect r0 == 3 * 3;
}

// REPEAT 3 - TIME: 10.1772119 s

method {:test} Test12() {
expect 5926 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5926);
expect r0 == factorial(5926);
}
method {:test} Test13() {
expect 5926 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5926);
expect r0 == factorial(5926);
}
method {:test} Test14() {
expect 4 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(4);
expect r0 == 4 * 4;
}
method {:test} Test15() {
expect 4 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(4);
expect r0 == 4 * 4;
}

// REPEAT 4 - TIME: 12.230038 s

method {:test} Test16() {
expect 5927 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5927);
expect r0 == factorial(5927);
}
method {:test} Test17() {
expect 5927 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5927);
expect r0 == factorial(5927);
}
method {:test} Test18() {
expect 5 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(5);
expect r0 == 5 * 5;
}
method {:test} Test19() {
expect 5 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(5);
expect r0 == 5 * 5;
}

// REPEAT 5 - TIME: 14.0759106 s

method {:test} Test20() {
expect 5928 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5928);
expect r0 == factorial(5928);
}
method {:test} Test21() {
expect 5928 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5928);
expect r0 == factorial(5928);
}
method {:test} Test22() {
expect 6 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(6);
expect r0 == 6 * 6;
}
method {:test} Test23() {
expect 6 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(6);
expect r0 == 6 * 6;
}

// REPEAT 6 - TIME: 15.9218054 s

method {:test} Test24() {
expect 5929 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5929);
expect r0 == factorial(5929);
}
method {:test} Test25() {
expect 5929 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5929);
expect r0 == factorial(5929);
}
method {:test} Test26() {
expect 7 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(7);
expect r0 == 7 * 7;
}
method {:test} Test27() {
expect 7 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(7);
expect r0 == 7 * 7;
}

// REPEAT 7 - TIME: 17.7624497 s

method {:test} Test28() {
expect 5930 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5930);
expect r0 == factorial(5930);
}
method {:test} Test29() {
expect 5930 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5930);
expect r0 == factorial(5930);
}
method {:test} Test30() {
expect 8 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(8);
expect r0 == 8 * 8;
}
method {:test} Test31() {
expect 8 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(8);
expect r0 == 8 * 8;
}

// REPEAT 8 - TIME: 19.8684395 s

method {:test} Test32() {
expect 5931 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5931);
expect r0 == factorial(5931);
}
method {:test} Test33() {
expect 5931 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5931);
expect r0 == factorial(5931);
}
method {:test} Test34() {
expect 9 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(9);
expect r0 == 9 * 9;
}
method {:test} Test35() {
expect 9 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(9);
expect r0 == 9 * 9;
}

// REPEAT 9 - TIME: 21.7294872 s

method {:test} Test36() {
expect 5932 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact(5932);
expect r0 == factorial(5932);
}
method {:test} Test37() {
expect 5932 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFact2(5932);
expect r0 == factorial(5932);
}
method {:test} Test38() {
expect 10 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare(10);
expect r0 == 10 * 10;
}
method {:test} Test39() {
expect 10 >= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sqare2(10);
expect r0 == 10 * 10;
}

// REPEAT 10 - TIME: 23.3219333 s
