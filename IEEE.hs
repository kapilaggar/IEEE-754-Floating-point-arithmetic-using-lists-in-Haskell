
--------------------------- Single or Double Precision ------------

exponent_bits = 7
fractional_bits = 23
----------------------      Convert number to ieee754 format       ---------------------- 
convert_to_ieee number
        | number ==0 = zero
        | otherwise = (sign,ex,frac)
                        where  sign = if number < 0 then 1 else 0
                               frac = ieee754_fractional f 
                               ex =  ieee754_exponent (2^exponent_bits + e -1)
                               f = head x
                               x = until_one (abs number)
                               e= if (abs number) > 1 then length x-1 else (-1) * length x +1

--get the number of divisions or multiplications required to make the number in format 1.xx * 2**y
until_one number = if number > 1 then get_one number else get_one' number

get_one number
  | number<2  = [number-1]
  |otherwise = get_one (number/2) ++ [number]

get_one' number
  |number>1  = [number-1]
  |otherwise = get_one' (number*2) ++ [number]


ieee754_exponent:: Int -> [Int]
ieee754_exponent x =take (8-length binary_representation) (repeat 0) ++ binary_representation 
                    where binary_representation= int_to_binary x

ieee754_fractional::(Eq a,Ord a,Num a)=> a -> [Int]
ieee754_fractional num = take fractional_bits $ fractional_to_binary num ++ (repeat 0)


--convert integer to binary
int_to_binary:: Int -> [Int]
int_to_binary x = if (x==0) then [] else int_to_binary (div x 2) ++ [(mod x 2)]

fractional_to_binary ::(Eq a,Ord a,Num a)=> a -> [Int]
fractional_to_binary 0=[0]
fractional_to_binary num
 | num*2 >= 1 = 1:fractional_to_binary (num*2 -1)
 | num*2 < 1 = 0:fractional_to_binary (num*2)

---------------------    Convert ieee754 to human readable format   ----------------------

convert_from_ieee (sign,ex,frac) =((-1)^sign) * (2**(binary_to_dec ex-(2^exponent_bits -1)))  *(1+ binary_to_frac frac)

--convert binary to decimal
binary_to_dec :: ( Num a) => [Int] -> a
binary_to_dec x = sum $map snd $ filter ((==1).fst) $zip (reverse x) $map (2^) [0,1..]

--convert binary to fractional
binary_to_frac :: (Fractional a) => [Int] -> a
binary_to_frac frac = sum $map snd$ filter ((==1).fst)  $zip frac $ map (1/) $map (2^) [1..]

----------------------------------------------------------------------------------------------------


number1=(0,[1,0,0,0,0,0,1,0],[0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1])
number2=(0,[1,0,0,0,0,0,1,0],[0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0])
zero =(0,[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])
inf=(0,[1,1,1,1,1,1,1,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])

--Boundary Values

iszero ::(Int,[Int],[Int])->Bool
iszero (a,b,c)=(a==0) && (b==[0,0,0,0,0,0,0,0]) && (c==[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])

isinf :: (Int,[Int],[Int])->Bool
isinf (a,b,c)= (a==0) && (b==[1,1,1,1,1,1,1,1]) && (c==[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])

--Gates
iand :: Int ->Int ->Int
iand 0 y =0
iand 1 y =y

ior :: Int ->Int ->Int
ior 1 y = 1
ior 0 y = y

ixor :: Int ->Int ->Int
ixor x y
 | x==y = 0
 | otherwise = 1

inot 0 = 1
inot 1 = 0

--Circuits

--Adders
-- sum carry
halfadder x y = (ixor x y,iand x y )
fulladder x y z =(ixor z (ixor x y), ior  (iand x y) (iand z (ixor x y)))
addnum x y = reverse (iadd (reverse x) (reverse y) 0)

-- when all data bits are consumed
iadd [] [] carry
 | carry ==0 =[]
 | otherwise =[1]


iadd (x:xs) (y:ys) carry = [fst z] ++ iadd xs  ys (snd z)
 where z=fulladder x y carry

--subtractors
-- diff borrow
halfsubtractor x y = (ixor x y,iand (inot x) y )
fullsubtractor x y z =(ixor z (ixor x y), ior  (iand (inot x) y) (iand z (inot (ixor x y))))
subnum x y = reverse (isub (reverse x) (reverse y) 0)

--when all bits are consumed
isub [] [] borrow
 | borrow ==0 =[]
 | otherwise =[1]

isub (x:xs) (y:ys) borrow = [fst z] ++ isub xs  ys (snd z)
 where z=fullsubtractor x y borrow

--Multipliers
prod y x = map (*x) y

imul x y =addall $ cal z (length z)
 where z=multiplier (reverse x) y

multiplier [] y = []
multiplier (x:xs) y = (prod y x):(multiplier xs y)

cal z l =[ x | a<-[0..(l-1)],x<-[(replicate (l-a) 0 )++ z!!a ++ (replicate a 0 )]]
addall arr = foldl1 addnum arr

--multiply first second
multiply (a,b,c) (p,q,r)
 | iszero (a,b,c) =zero
 | iszero (p,q,r) =zero
 | isinf (a,b,c) = inf
 | isinf (p,q,r) =inf
 | otherwise = (ixor a p,lastN 8 (normalizeExp (0:b) (0:q) z)  ,normalizeMantisa z)
  where z=imul (1:c) (1:r)

normalizeMantisa (z:zs)
 | z==0 = take 23 (drop 1 zs)
 | otherwise = take 23 (drop 1 (z:zs))

normalizeExp p q (z:zs)
 | z==0 = subnum (addnum p q)  [0,0,1,1,1,1,1,1,1]
 | otherwise =addnum (addnum (subnum p [0,0,1,1,1,1,1,1,1]) q) [0,0,0,0,0,0,0,0,1]

lastN n xs = drop (length xs - n) xs

icompare [] [] = 0
icompare (x:xs) (y:ys)
 | x >y = 1
 | y>x  = -1
 | x==y  = icompare xs ys


addition (a,b,c) (p,q,r)
 | iszero (a,b,c) =(p,q,r)
 | iszero (p,q,r) =(a,b,c)
 | isinf (a,b,c) = inf
 | isinf (p,q,r) =inf
 | otherwise = iaddition (a,b,c) (p,q,r)

iaddition (a,b,c) (p,q,r)
 | icompare b q == 0 = valadd (a,b,1:c) (p,q,1:r)
 | icompare b q > 0 = valadd (a,b,1:c) (shift (a,b,c) (p,q,r))
 | icompare b q < 0 = valadd (shift (a,b,c) (p,q,r)) (p,q,1:r)

shift (a,b,c) (p,q,r)
 | icompare b q > 0 =(p,b,take 24 (replicate (binary_to_dec (subnum b q) )  0 ++ [1]++ r) )
 | otherwise = (a,q,take 24 (replicate (binary_to_dec (subnum q b) )  0 ++ [1]++ c) )

--shift (a,b,c) (p,q,r)
-- | icompare b q > 0 =(p,b,take 24 ([0]++replicate (bintodecbefore (subnum b q) -1)  0 ++ [1]++ r) )
-- | otherwise = (a,q,take 24 ([0]++replicate (bintodecbefore (subnum q b) -1)  0 ++ [1]++ c) )


valadd (a,b,c) (p,q,r)
 | a==p = (a,addnum b (snd y),(fst y))
 | otherwise = valsub (a,b,c) (p,q,r)
  where y= normalize  (addnum c r) [0,0,0,0,0,0,0,0]

normalize [] val =([],val)
normalize (x:xs) val
 | length (x:xs) >24 = (take 23 xs,[0,0,0,0,0,0,0,1]) --occur only when there is a carry
 | x==0 = normalize (xs++[0]) (addnum val [0,0,0,0,0,0,0,1])
 | x==1 = (xs, val)


valsub (a,b,c) (p,q,r)
 | icompare c r == 0 = zero
 | icompare c r >0 = valminus (a,b,c) (p,q,r)
 | icompare c r <0 = valminus (p,q,r) (a,b,c)

valminus  (a,b,c) (p,q,r) = (a,subnum b (snd y),fst y)
 where y = normalize (subnum c r )  [0,0,0,0,0,0,0,0]

substract (a,b,c) (p,q,r)
 | iszero (a,b,c) =(inot p,q,r)
 | iszero (p,q,r) =(a,b,c)
 | isinf (a,b,c) = inf
 | isinf (p,q,r) =inf
 | otherwise = iaddition (a,b,c) (inot p,q,r)
