\\ Independently recompute both cubic models, both unit characters and the dilogarithm.
number(s)=fromdigits(vector(#s,i,Vecsmall(s)[i]-48));
checkrow(row)={
  my(p=row[1],m=p^2, roots=polrootspadic(x^3+x^2-2*x-1,p,3));
  my(tvals=vector(3), units=vector(3), coords=vector(3), traces=vector(3), found=0);
  for(i=1,3,
    my(th=Mod(lift(roots[i]),m),d1=2-th,d2=4-th^2,d3=1+th+th^2);
    my(T=if(row[2],(d2-d3)/(d2-d1),th+2),u=T*(T-1),W=if(row[2],2*d3-d1-d2,2*d2-d1));
    coords[i]=lift(th)%p; tvals[i]=(lift(T^(p-1))-1)/p; units[i]=(lift(u^(p-1))-1)/p;
    traces[i]=lift(W*u/(2*T-1)^3)%p;
    if(coords[i]==row[3],
      my(t=lift(T)%p, first=lift((1-Mod(t,m)^p-Mod(1-t,m)^p))/p, second=0, b=Mod(t,p), v=1);
      \\ Fermat gives j^(p-3)=j^(-2) in the residue field.
      for(j=1,p-1,v*=b;second+=v*Mod(j,p)^(p-3));
      if([t,tvals[i],units[i],traces[i],lift(2*second-tvals[i]*first)]!=[row[4],row[5],row[6],row[8],row[9]],error("witness ",p));
      found=1
    )
  );
  my(order=vecsort(coords,,1));
  if(!found || vecmin(traces)==0 || vecmin(units)==0 || !row[5] || !row[7] || !row[9],error("zero entry ",p));
  if((tvals[order[1]]*units[order[2]]-tvals[order[2]]*units[order[1]])%p!=row[7],error("minor ",p));
}
{my(lines=readstr("certificates.txt"));for(i=1,#lines,checkrow(apply(number,strsplit(lines[i]," "))));if(#lines!=328,error("row count"));print(#lines," independent split-prime certificates");}
