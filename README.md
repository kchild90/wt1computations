This repository includes the dimensions of weight 1 newforms, and the coefficients up to at least the Sturm bound of weight 1 forms in spaces where the exotic subspace is non-zero.

The file wt1_forms_dims.txt is a list of dimensions of weight 1 newform spaces, in the format l:c:d where l is the level of the newform, c is the Conrey logarithm of the newform and d is the dimension of the newform space.
Only one character is listed for each Galois orbit. So for instance the line:
52:[1, 4]~:1
Corresponds to the space https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/52/1/j/a/3/1/. This character has order 6, and so there is a conjugate space, also of dimension 1, which is not listed. The resultant full dimension across the orbit (important for computing Gamma_1 forms) is 2.

In the wt1satakes folder are separate files for each level N. In each file, the Satake parameters are given up to a prime p, the greatest prime less than or equal to max(30sqrt(N),Sturm bound) of eigenform bases for newform spaces where the exotic subspace is non-zero. Each line gives the character, again as a Conrey logarithm, followed by the GCD of the denominators of all Satake angles, followed by a vector of numerators of Satake angles. Let p be the n-th prime, d be the GCD of Satake angle denominators, and b be the n-th element in the vector. If p doesn't divide N, then a_p is given by exp(2pi i b/d) + chi(p)/exp(2pi i b/d). If p does divide N, and b>-1, then a_p=exp(2pi i b/d). Finally, if p divides N, and b=-1, then a_p=0. Thus, all a_p are recovered from Satake angles, and all a_n are recovered by applying Hecke relations. These can also be computed over a finite field by fixing an h-th primitive root of unity in the field, where h=LCM(b, Ord(chi)).

Alternatively, in the wt1coefs folder are files giving these explicit Fourier expansions over cyclotomic fields. Each line gives the character, followed by an integer n, followed by a vector of coefficients, starting at a_1, given as polynomials in x where x is zeta_n. Note that fixing a specific embedding of x into C also fixes the character. Therefore, if embedding multiple forms with the same character, care must be taken to ensure the embeddings are conformal. This can be achieved by mapping x to exp(2pi i/n).

The computation is comprehensive up to level 10,000.
