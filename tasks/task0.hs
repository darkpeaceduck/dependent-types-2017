-- 0. Напишите на хаскеле тип, соответствующий следующим формулам, и предъявите элемент этого типа (тем самым доказав, что эта формула верна):
-- a. (P -> R) -> (Q -> R) -> P or Q -> R

-- b. (P and Q -> R) -> P -> Q -> R
-- c. (P -> Q -> R) -> P and Q -> R

-- d. (P or Q -> P and Q) -> (P -> Q) and (Q -> P)

-- e. ((P -> Q -> R) -> P) -> (P -> R) -> R
-- f. ((((P -> Q) -> P) -> P) -> Q) -> Q

atype :: (p -> r) -> (q -> r) -> (Either p q) -> r
atype a b (Left p) = (a p)
atype a b (Right q) = (b q)


btype :: ( (p, q) -> r) -> p -> q -> r
btype f a b =  f (a, b)

ctype :: (p -> q -> r) -> (p, q) -> r
ctype a b = a (fst b) (snd b)

dtype :: ((Either p q) -> (p, q)) -> ((p -> q), (q -> p))
dtype f = (\p -> snd (f (Left p)), \q -> fst (f (Right q)))

etype :: ((p -> q -> r) -> p) -> (p -> r) -> r
etype f  b = b (f (\p q -> b p))

ftype :: ((((p -> q) -> p) -> p) -> q) -> q
ftype f = f (\f' -> f' (\p -> f (\_ -> p)))


