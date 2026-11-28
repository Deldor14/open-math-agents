z = Mod(x,polcyclo(13));
t = z+z^-1;
R = (2-z^6-z^(-6))/(2-t);
U = R*(R-1); Y0 = 2*R-1;
vals = vector(6,j,trace((2*(2-z^(6*j)-z^(-6*j))-(2-z^j-z^(-j)))*U/Y0^3)/2);
if(vals!=[-91,1521,416,-52,-195,1053],error("incorrect traces"));
print("Half traces from the full cyclotomic field: ",vals);
q = Mod(Mod(1,121)*x,polcyclo(13));
pass = select(a->(a+1)%11 && (a+1)*(a+q)^11==(a+1)^11*(a+q^11),[0..120]);
if(pass!=[0],error("affine Frobenius check"));
if(((q-1)^12/13)^11==(q^11-1)^12/13,error("exceptional Frobenius check"));
print("Frobenius test modulo 121: affine slope 0 only; exceptional case excluded");
quit
