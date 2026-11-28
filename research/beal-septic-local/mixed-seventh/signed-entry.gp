\\ Frobenius coefficient intersections in F_p[X] for a nonzero projective slope.
residuepoly(p,j) = Polrev(vector(1+(p-1-j)\7,k,1/Mod(j+7*(k-1),p)));
checkprime(p) = {
  my(d=0, subgroup=(p-1)/gcd(7,p-1));
  for(j=1,6, if(j!=p%7,
    d=gcd(d,residuepoly(p,j));
    if(poldegree(d)==0,break)
  ));
  if(poldegree(d)>0,
    d=gcd(d,lift(Mod(x,d)^subgroup)-1);
    if(poldegree(d)>0,
      if(poldegree(d)!=1 || subst(d,x,1)!=0 || gcd(7,p-1)!=1,
        error("ordinary residual root at ",p," in ",d))
    )
  );
  my(m=p^2,z=Mod(x,polcyclo(7)*Mod(1,m)),v=(z-1)^6/7);
  if(v^p==(z^p-1)^6/7,error("exceptional slope at ",p));
  return(1)
}
{my(n=0,s=0); forprime(p=11,20000,n+=checkprime(p);s+=p-2);
print(n," primes; ",s," nonzero finite slopes with unit sum; exceptional slopes excluded")}
