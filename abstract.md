This submission formalizes Nguyen, Scott, and Seymour's proof that the
five-vertex path $P_5$ has the [Erdős–Hajnal property](https://laxarchive.org/lax-57/paper.html#m1). It proves that there is
a positive integer $q$ such that every finite graph $G$ with no induced copy
of $P_5$ satisfies

$$
|V(G)| \leq \max\{\alpha(G),\omega(G)\}^{q}.
$$

The formalization follows the paper's blockade argument through polynomial
[semisparse blockades in house-free graphs](https://laxarchive.org/lax-57/paper.html#m4), the
[sparse-house trichotomy](https://laxarchive.org/lax-57/paper.html#m13) and its
[iteration](https://laxarchive.org/lax-57/paper.html#m19), and a final critical-graph argument. Density inequalities are
stated over the natural numbers with denominators cleared. The proof
uses [Rödl's theorem](https://laxarchive.org/lax-57/paper.html#m2),
[sparse thinning](https://laxarchive.org/lax-54/paper.html#m10),
[maximum-degree reduction](https://laxarchive.org/lax-54/paper.html#m12), and the
[bipartite comb lemma](https://laxarchive.org/lax-57/paper.html#m8) from
[lax-54](https://laxarchive.org/lax-54/). Every argument
specific to $P_5$ and its complement is proved in this submission.
