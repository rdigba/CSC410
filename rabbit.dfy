function method unpair(n: nat): (nat, nat)
{
    // Add an implementation for this
    if n == 0 then (0, 0) else
    if n == 1 then (1, 0) else
    var (x, y) := unpair(n-1);
    if x == 0 then (y+1, 0) else
    (x-1, y+1)
}

function method pick(i: nat): nat
{
  var (x, y) := unpair(i);
  x + i * y // a + t * b
} 

lemma findTForAB(a: nat, b: nat)  
decreases a+b,b
  requires a >= 0 && b >= 0
  ensures exists n: nat :: unpair(n) == (a,b)
{
  if a == 0 && b == 0 {
    calc == {
      unpair(0);
      (0,0);
      (a,b);
    }
  } else if a == 1 && b == 0 {
    calc == {
      unpair(1);
      (1,0);
      (a,b);
    }
  } else { 
      if b == 0 {
        findTForAB(0, a-1); 
        var k: nat:| unpair(k) == (0,a-1); // From induction hypothesis
        assert unpair(k+1) == (a, 0); // From function recursion definition
        // wts unpair(k+1) 
        calc == {
          (a,b);       
          (a,0);
          unpair(k+1);
        }
      } else // b != 0 && a != 0
      {
        findTForAB(a+1, b-1);
        var k: nat:| unpair(k) == (a+1, b-1); // From induction hypothesis
        assert unpair(k+1) == (a, b); // From function recursion definition
        calc == {
          (a,b);
          unpair(k+1);
        }
      }
  }
}

method catchTheRabbit(a: nat, b: nat)
{
var t := 0;
  // prove that this loop terminates and therefore the rabbit is caught
  findTForAB(a,b);    
  var n: nat:| (a,b) == unpair(n);
  while a + t * b != pick(t)  
    invariant t <= n;
    decreases n - t;  
    { t := t + 1; }
}
