method {:testEntry} mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=0;
	while (r+1)*(r+1) <=n
	 invariant r>=0 && r*r <=n
	  decreases n-r*r
	 {
	   r:=r+1;
	 }


}


method {:testEntry} mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=n;
	while n<r*r
	invariant 0<=r<=n && n<(r+1)*(r+1)//write the invariant
	invariant r*r<=n ==> n<(r+1)*(r+1)
	decreases r//write the bound
	{
		r:=r-1;
	}


}

method {:testEntry} mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{   var y:int;
    var h:int;
    r:=0;
	y:=n+1;
	//Search in interval [0,n+1) 
	while (y!=r+1) //[r,y]
	  invariant r>=0 && r*r<=n<y*y && y>=r+1//	write the invariant 
	  decreases y-r//write the bound
	 {
	   h:=(r+y)/2;
	   if (h*h<=n)
	     {r:=h;}
	   else
	     {y:=h;} 
	 }


}

method {:test} Test36() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}
method {:test} Test37() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}
method {:test} Test38() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 19.6850955 s
