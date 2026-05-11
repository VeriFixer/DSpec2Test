//Mac/Linux: make
//Windows: dotnet build Source/Dafny.sln

//../Binaries/dafny generate-tests Spec "Example1.dfy" > "Example1Tests.dfy"

method {:testEntry} Classify(x: int) returns (r: int)
  ensures x < 0 ==> r == -1
  ensures x == 0 ==> r == 0
  ensures x > 0 ==> r == 1
  {
    if x < 0{
      r := -1;
    } 
    else if x == 0 {
      r := 0;
    }
    else {
      r := 1;
    }
  }

