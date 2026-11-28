\\ Direct product in the degree-156 local field over Q13.
weight13(z)={
  my(f=lift(z),v=10000);
  for(i=0,12,my(c=lift(polcoef(f,i,x)));for(j=0,11,
    my(k=polcoef(c,j,y));
    if(padicprec(k,13)<3,error("insufficient coefficient precision"));
    if(k!=0,v=min(v,156*valuation(k,13)+12*i+13*j))));
  v
}
{
  my(p=13,theta=polrootspadic(x^3+x^2-2*x-1,p,40)[1]);
  if(lift(theta)%p!=7,error("unexpected root order"));
  my(d1=2-theta,d2=4-theta^2,d3=1+theta+theta^2,T=(d2-d3)/(d2-d1),t=lift(T)%p);
  my(E=Mod(x,(x+t)^p-T),pi0=Mod(y,subst(polcyclo(13),x,1+y)),z=1+pi0);
  my(b=t+E,eta=pi0/E,product=1+0*E);
  for(i=1,p-1,product*=((1-z^i*b)/sum(j=0,i-1,z^j))^i);
  my(unit=lift(Mod(polcoef(lift(polcoef(lift(product),0,x)),0,y),p)));
  product/=unit^p;
  if(weight13(product-1)!=143,error("initial weight"));
  my(v=vector(p,j,weight13(product-(1+(j-1)*eta^11)^p)));
  if(vecmax(v)!=155 || sum(i=1,p,v[i]==155)!=1,error("last weight"));
  print("T mod 169 = ",lift(T)%169,", all root corrections: ",v)
}
