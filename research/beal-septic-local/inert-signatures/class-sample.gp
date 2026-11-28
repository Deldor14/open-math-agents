\\ Certified  p-primary class groups of Q(zeta_7)^+ Q(zeta_p) at inert p.
{forprime(p=11,5000,if(p%7==1 || p%7==6,next);my(h=lift(chinese(Mod(-1,7),Mod(1,p))),v=subcyclopclgp([7*p,[h]],p,0));print(p," ",v[2][1]," ",v[3][1]));}
