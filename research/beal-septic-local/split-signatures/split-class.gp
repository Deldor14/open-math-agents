\\ Independent test for p dividing the relative class number of K(zeta_p).
\\ A degree zero gcd in both columns means p does not divide that number.
classTest(p)={
  my(g=lift(znprimroot(p)), n=p-1, m=p^2, tg=lift(Mod(g,m)^p));
  my(axes=[[0,0],[1,0],[-1,-1],[0,1],[0,1],[-1,-1],[1,0]]);
  my(twists=vector(7,i,sum(j=0,6,j*axes[1+(i-1+j*p)%7])));
  my(terms=vector(n), first=vector(n), second=vector(n), a=1, ta=1);
  for(i=1,n,
    terms[i]=(a-ta)/p;
    first[i]=twists[1+a%7][1]; second[i]=twists[1+a%7][2];
    a=a*g%p; ta=ta*tg%m
  );
  my(F=Polrev(terms)*Mod(1,p), A=Polrev(first)*Mod(1,p), B=Polrev(second)*Mod(1,p));
  my(P=(x^(n/2)+1)*Mod(1,p), exceptional=x-Mod(g,p)^(-1));
  my(ordinary=poldegree(gcd(F,P/exceptional)), twisted=poldegree(gcd(A^2-A*B+B^2,P)));
  [ordinary,twisted]
}
{forprime(p=11,20000,if(p%7!=1 && p%7!=6,next);my(v=classTest(p));print(p," ",v[1]," ",v[2]));}
