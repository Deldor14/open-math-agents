check_principal_norms(B, lower, upper) = {
  my(T=2^22, count=0);
  if(B.pol != x^21+2*x^14-16*x^7+8 || B.disc != -2^18*7^21*13^14,
     error("unexpected field"));
  forprime(q=lower, upper,
    my(degrees=logint(T-1,q), plist=idealprimedec(B,q,degrees));
    for(j=1,#plist,
      my(pr=plist[j], N=q^pr.f, g=bnfisprincipal(B,pr,3)[2]);
      if(type(g)!="t_COL" || #g!=21 || denominator(g)!=1,
        error("nonintegral candidate",[q,j]));
      if(abs(nfeltnorm(B,g))!=N || nfmodpr(B,g,pr)!=0,
        error("norm or residue mismatch",[q,j]));
      print(N); count++;
    );
  );
  print("count ",count);
}
