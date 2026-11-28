\\ Direct wild Frobenius tests for signed integer bases in the range of DS Proposition 4.1.
entry(p)={
  my(m=p^2,z=Mod(x,polcyclo(7)*Mod(1,m)),zp=z^p,slopes=List());
  for(t=0,m-1,if((t+1)%p && (t+1)*(t+z)^p==(t+1)^p*(t+zp),listput(slopes,t)));
  if(Vec(slopes)!=[0] || ((z-1)^6/7)^p==(zp-1)^6/7,error("entry ",p));
  print(p," signed entry passed")
}
{foreach([13,29,41,43,71,83],p,entry(p))}
