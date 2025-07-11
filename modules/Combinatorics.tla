Write a module to support two operators for natural numbers.
Factorial computes the product of all positive integers up to n, with 0! defined as 1.
Choose computes (n choose k), representing combinations of k items from n items.

------------------------- MODULE Combinatorics -------------------------
EXTENDS Naturals

factorial[n \in Nat] == 
    IF n = 0 THEN 1 ELSE n * factorial[n-1]

choose(n, k) ==
    factorial[n] \div (factorial[k] * factorial[n - k])

=========================================================================