
//a first implementation of the datatype. Let's forget about phase here.
//otherwise, we can add one form field for the phase value below.
datatype Q (n:nat)) = Nor Vector(bool)[n] | Had Vector(int)[n] | CH (m:nat) Vector(bool)[m][n]

//turn the Nor vector (n bit) to a Had Vector of int. If x[i] = 0 originally, then x[i] -> 1 (new) if x[i]=1, then x[i] -> -1
x := nor_to_had(x,n); 


// nor_to_ch turns a list of sessions in Nor to a list of sessions in ch.
//any data Nor x]n] can be viewed as CH 1 x[0][n] where 1 represents the number of possibility in the entanglement
//if it is one, then there is only one case, and then the entanglement is Nor.
//another observation is that.
//in an entanglement x[0..i],y, it is usually the case that x[0..i] is saturation
//So, you just do not need to record x[0..i] in CH, and it is just an index for the vector in CH.
(y) := nor_to_ch_one(y,n); 

//take a index in x,
//then the session x[i],y have a type of CH (m+2^m) ..
//here we can replace x[i],y with a new variable z.
//the result is z = |0,left> + |1,right>
(x[0..i],y) := ch_update(x, i, x[0..i-1],y,n, left, right); 



method Shor ( a : int, N : nat, n : nat, yv : int, x : Q[n], y : Q[n] ) returns ( xv: int )
  requires (n > 0)
  requires ( forall i, i >= 0 && i < n ==> y[i] == q0) 
  ensures (a^xv mod N == yv)
{
  x *= H ; // this can be a function
  x := nor_to_had(x,n); //turn type of x from Nor to Had. 
  y[0] *= X; //y keeps in Nor but now, we notice that y = 1.

  (y) := nor_to_ch(y,n); //turn y to ch from now.
  for (int i = 0; i < n; x[i]; i ++)
    invariant (i <= n)
    invariant (1 < N)
    invariant (saturation(x[0..i]))
    invariant (type(x[0..i],y) = ch (2^i) (\lambda k. (k,a^k mod N)))
    // this amounts to say
    // forall k | 0 <= k < i :: x[0..i].m.c[k].0 == k && y.m.c[k].0 == Pow(a, k) & N
    invariant ((x[0..i],y) == psum(k=0,2^i,(k,a^k mod N)))
  {
    (x[0..i],y) := ch_update(x,i, x[0..i-1], y, n+i, y, classic(a^(2^i) * y mod N)); //compile with adding ch_update
  }

  //partial measruement is still in CH, but the n number is shrinked, so need to think about a representation.
  pmeasure(y,yv);
  //applying RQFT to x that is in CH will result in still a CH state that changes the phase value.
  //will have special treatement.
  x *= RQFT;
  float p =0;
  (p,xv)= measure(x);
}

//need lib theory:
//f(y,f(x,b)) = f(x+y,b)
//saturation(x[0..i]) ==> saturation(x[i+1]) 
// ==> if x[i+1] then psum(k=0,2^(i+1),(k+2^i,f(2^i,f(k,b))) else psum(k=0,2^i,(k,f(k,b))) = psum(k=0,2^(i+1),f(k,b))

//saturation(x[0..i]) ==> saturation(x[i+1]) 
// ==> if x[i+1] then ch (2^(i+1)) (\lambda k. (k+2^i,f(2^i,f(k,b))) 
//   else ch (2^i) (\lambda k. (k,f(k,b)) = ch (2^(i+1)) (\lambda k. (k,f(k,b))
