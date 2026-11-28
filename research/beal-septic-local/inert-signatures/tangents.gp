\\ Evaluate the actual Kummer coefficient in several distinct residue fields.
testTangent(p)={
  my(t=ffgen((x^3+x^2-2*x-1)*Mod(1,p),'t), g=(p-1)/2);
  my(u=(t+1)*(t+2), W=6+t-2*t^2, y0=2*t+3, d=u^(p^2));
  my(Z=vector(g,i,if(i==g,t,i+1)), r=vector(g,i,(Z[i]^2-1)/(4*d)));
  my(Y=vector(g,i,Z[i]^p), T=vector(g,i,(Y[i]+1)/2));
  my(mat=matrix(g,g,j,i,r[i]^(j-1)/Y[i]), target=vectorv(g,j,j*W/y0));
  my(b=matsolve(mat,target));
  my(L=sum(i=1,g,u/(Y[i]*T[i])*(b[i]^p-r[i]^(p-1)*b[i])));
  my(expect=if(p%7==2 || p%7==5,3,4));
  if(L+L^p+L^(p^2)!=expect,error("Kummer trace at ",p)); print(p," ",g," ",expect)
}
{forprime(p=11,100,if(p%7!=1 && p%7!=6,testTangent(p)));}
