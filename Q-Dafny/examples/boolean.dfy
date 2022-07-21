//assume constants, left, right, down
//assume constants root, nroot, and other node numbers
method Boolean ( n : int, x : Q[n], y : Q[n], coin : Q[2] ) returns ( xv: int )
  requires (n > 0)
  requires ( forall i, i >= 0 && i < n ==> x[i] == q0) 
  requires ( forall i, i >= 0 && i < n ==> t[i] == q0) 
  requires ( forall i, i >= 0 && i < n ==> coin[i] == q0) 
  ensures (xv == 0 <-> eval(y) == false) //finally if xv == 0 then the boolean y is evaluated to false.
{
  x *= H ;
  classic(phase((3/2)*x)); //put the global phase e^{2 pi i (1/2^1 + 1/2^2)} on x.
  classic(y <- root);
  classic(coin <- left);

  //need to finish the invariant. 
  //the input X is in Had type, y and coin are in Nor.
  //after one step, (y.coin) are entangled, and x is Had, so (x,y,coin) are entangled (CH)
  qwhile (int i = 0; i < n; x < i; i ++)
  invariant (i <= n)
{
  //the first two is the type [11] is a left,[00] is root, [01] is nroot, [10] is others
  if (y[0] && y[1]) classic(phase(test(y[2..n])));
  if (y[0] && not y[1]) distr(coin,1/3 * left + 1/3 * right + 1/3 * down);
  if (not y[0] && y[1]) reflect(coin,1/10 * down + 9/10 * left);

  //walk step in quantum walk. flip coin and y to include more nodes.
  //Remember coin is in CH now because of the distribution/relfection above.
  //coin = CH and y = Nor, so (y,coin) are entangled after. 
  classic(
  if(coin[1]) {coin[0] *= X ; down(y)};
  if(not coin[1]) {up(y,coin[0])};
  coin[1] *= X;
  );
  
}

x *= RQFT;
float p =0;
(p,xv)= measure(x);
}
