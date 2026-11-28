\\ Second relative class-number check. Explicitly evaluate every odd character.
\\ Vector indices in GP start at 1. Characters modulo 7 take values 1,J,J^2.
oddValues(coeff,g,p,kernel,phase)={
  my(h=(p-1)/2, a=vector(h,i,(coeff[i]-coeff[i+h])*phase[i]%p));
  my(product=lift((Polrev(a)*Mod(1,p))*kernel));
  vector(h,j,polcoef(product,j+h-2))
}
individual(p)={
  my(g=lift(znprimroot(p)), h=(p-1)/2, w=g^2%p, n=p-1);
  my(index=vector(p), ordinary=vector(n), c=vector(n), d=vector(n), a=1);
  for(i=1,n,index[a]=i; ordinary[i]=(g*a)\p; a=a*g%p);
  for(t=1,7*p-1,
    if(t%p==0 || t%7==0,next);
    my(i=index[t%p], r=t%7);
    if(r==1 || r==6,c[i]+=t,if(r==2 || r==5,d[i]+=t,c[i]-=t;d[i]-=t))
  );
  c=c/p; d=d/p;
  if(denominator(c)!=1 || denominator(d)!=1,error("nonintegral character sum"));
  my(phase=vector(h), invphase=vector(2*h-1));
  my(step=g, z=1);
  for(i=1,h,phase[i]=z; z=z*step%p; step=step*w%p);
  my(win=Mod(w,p)^(-1));
  for(j=1,2*h-1,my(k=j-h);invphase[j]=lift(win^(k*(k+1)/2)));
  my(kernel=Polrev(invphase)*Mod(1,p));
  my(v=oddValues(ordinary,g,p,kernel,phase), A=oddValues(c,g,p,kernel,phase), B=oddValues(d,g,p,kernel,phase));
  my(s=0,t=0);
  for(j=1,h,if(j!=h && v[j]%p==0,s++);if((A[j]^2-A[j]*B[j]+B[j]^2)%p==0,t++));
  [s,t]
}
{forprime(p=11,20000,if(p%7==1 || p%7==6,next);my(v=individual(p));print(p," ",v[1]," ",v[2]));}
