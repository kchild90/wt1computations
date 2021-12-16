This repository includes the dimensions of weight 1 newforms, and the coefficients up to at least the Sturm bound of weight 1 forms in spaces where the exotic subspace is non-zero.

The file wt1_forms_dims.txt is a list of dimensions of weight 1 newform spaces, in the format l:c:d where l is the level of the newform, c is the Conrey logarithm of the newform and d is the dimension of the newform space.
Only one character is listed for each Galois orbit. So for instance the line:
52:[1, 4]~:1
Corresponds to the space https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/52/1/j/a/3/1/. This character has order 6, and so there is a conjugate space, also of dimension 1, which is not listed. The resultant full dimension across the orbit (important for computing Gamma_1 forms) is 2.

In the wt1coefs folder are separate files for each level N. In each file, the coefficients are given up to max(30sqrt(N),sturm-bound) of eigenform bases for newform spaces where the exotic subspace is non-zero. Each line gives the character, again as Conrey logarithm, followed by the minimal cyclotomic field containing the coefficient field K, given as n where K=Q(zeta_n), followed by a vector of coefficients, starting at a_1, given as polynomials in x where x is zeta_n. If n is not 1, it is the maximal integer such that K=Q(zeta_n).
Note that again we only give one representative space of each Galois orbit, and that fixing a specific embedding of x into C also fixes the character. Therefore, if embedding multiple forms with the same character, care must be taken to ensure the embeddings are conformal. This can be achieved by mapping x to exp(2pii/n).

The computation is comprehensive up to level 10,000.
