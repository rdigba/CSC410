function gcd(a: nat, b: nat): nat
   requires a > 0 && b > 0
{   
   if a == b then a else
   if b > a then gcd(a,b - a) else
    gcd(a - b,b) 
}

predicate divides(a: nat, b:nat)
   requires a > 0 
{
  exists k: nat :: b == k * a
}

lemma dividesHelper(a: nat, b: nat, k: nat)
   requires a > 0 &&  b > 0 && k > 0 && b > a
   requires divides(k, a) && divides(k, b)
   ensures divides(k, b-a)
{
   var m :| a == m * k;
   var n :| b == n * k;
   assert(a == k * m);
   assert(b == k * n);
   // WTS exists x :: b - a == x * k
   var x :| n - m == x;
   calc == {
      b - a;
      k*n - k*m;
      k*(n - m);
      x*k;
   }
}
   
lemma dividesGCD(a: nat, b:nat, k: nat) 
    requires a > 0 &&  b > 0 && k > 0 
    requires divides(k, a) && divides(k, b)
    ensures divides(k, gcd(a,b))
{
   if a == b {
      
   } else if b > a {
      // show exists j :: gcd(a,b) == gcd(a,b-a) == k * j
      // assume k | gcd(a, b-a)
      // WTS k | gcd(a,b)
      dividesHelper(a, b, k);
      dividesGCD(a, b-a, k);
      assert(divides(k, gcd(a,b-a)));
      calc == {
         gcd(a,b);
         gcd(a,b-a);
      }
      assert(divides(k, gcd(a,b)));
   } else // a > b 
   {
      // Copy paste just flip stuff around
      dividesHelper(b, a, k);
      dividesGCD(a-b, b, k);
      assert(divides(k, gcd(a-b,b)));
      calc == {
         gcd(a,b);
         gcd(a-b,b);
      }
      assert(divides(k, gcd(a,b)));
   }
} 
