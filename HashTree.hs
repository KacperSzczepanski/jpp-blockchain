--Kacper Szczepański ks418474

module HashTree where

import Hashable32

data Tree a = Empty
            | Leaf Hash a
            | Node Hash (Tree a) (Tree a)

instance Show a => Show (Tree a) where
    show Empty = "Empty"
    show (Leaf h a) = "Leaf " ++ showHash h ++ " " ++ show a
    show (Node h l r) = "Node " ++ showHash h ++ " (" ++ show l ++ ") (" ++ show r ++ ")"

duplicateLastIfOdd :: [a] -> [a]
duplicateLastIfOdd list =
    if length list `mod` 2 == 0 then 
        list
    else
        list ++ [last list]


leaf :: Hashable a => a -> Tree a
leaf a = Leaf (hash a) a

twig :: Hashable a => Tree a -> Tree a
twig l = Node (hash (h, h)) l Empty where
    h = treeHash l

node :: Hashable a => Tree a -> Tree a -> Tree a
node l Empty = twig l
node l r = Node (hash (treeHash l, treeHash r)) l r

buildTree :: Hashable a => [a] -> Tree a
buildTree list = buildFromNodes $ map leaf list where
    buildFromNodes :: Hashable a => [Tree a] -> Tree a
    buildFromNodes list = if length list == 1 then head list else
        buildFromNodes $ makeNewLayer [] list where
            makeNewLayer :: Hashable a => [Tree a] -> [Tree a] -> [Tree a]
            makeNewLayer res [] = reverse res
            makeNewLayer res [t] = makeNewLayer (twig t : res) []
            makeNewLayer res list = makeNewLayer (node l1 l2 : res) (drop 2 list) where
                l1 = head list
                l2 = head $ tail list

treeHash :: Tree a -> Hash
treeHash (Leaf h _) = h
treeHash (Node h _ _) = h
treeHash _ = hash '0'

drawTree :: Show a => Tree a -> String
drawTree t = drawTree' 0 t where
    drawIndent :: Int -> String
    drawIndent n = replicate n ' '

    drawTree' :: Show a => Int -> Tree a -> String
    drawTree' indent t@(Leaf h a) = drawIndent indent ++ showHash h ++ " " ++ show a ++ "\n"
    drawTree' indent t@(Node h l Empty) = drawIndent indent ++ showHash h ++ " +\n" ++ drawTree' (indent + 2) l
    drawTree' indent t@(Node h l r) = drawIndent indent ++ showHash h ++ " -\n" ++ drawTree' (indent + 2) l ++ drawTree' (indent + 2) r
    drawTree' indent _ = "" 

{- | Building tree
>>> putStr $ drawTree $ buildTree "fubar"
0x2e1cc0e4 -
  0xfbfe18ac -
    0x6600a107 -
      0x00000066 'f'
      0x00000075 'u'
    0x62009aa7 -
      0x00000062 'b'
      0x00000061 'a'
  0xd11bea20 +
    0x7200b3e8 +
      0x00000072 'r'
-}

type MerklePath = [Either Hash Hash]
data MerkleProof a = MerkleProof a MerklePath

instance Show a => Show (MerkleProof a) where
    show (MerkleProof a path) = "(MerkleProof " ++ show a ++ " " ++ showMerklePath path ++ ")"
    showsPrec p (MerkleProof a path) = showParen (p > 10) $ showString $ "MerkleProof " ++ showsPrec 11 a ""  ++ (' ' : showMerklePath path)

buildProof :: Hashable a => a -> Tree a -> Maybe (MerkleProof a)
buildProof a t = checkPath a $ buildProof' a t [] where
    checkPath :: Hashable a => a -> MerklePath -> Maybe (MerkleProof a)
    checkPath _ [] = Nothing
    checkPath a path = Just (MerkleProof a path)

    buildProof' :: Hashable a => a -> Tree a -> MerklePath -> MerklePath
    buildProof' a (Empty) acc = []
    buildProof' a (Leaf h x) acc = if hash a == h then reverse acc else []
    buildProof' a (Node h l r) acc = if null resL then resR else resL where
        resL = buildProof' a l (Left (treeHash r) : acc)
        resR = buildProof' a r (Right (treeHash l) : acc)

merklePaths :: Hashable a => a -> Tree a -> [MerklePath]
merklePaths a t = merklePaths' a t [] []  where
    merklePaths' :: Hashable a => a -> Tree a -> MerklePath -> [MerklePath] -> [MerklePath]
    merklePaths' a (Empty) acc res = res
    merklePaths' a (Leaf h x) acc res = if hash a == h then (reverse acc) : res else res
    merklePaths' a (Node h l r) acc res = res2 where
        res1 = merklePaths' a r (Right (treeHash l) : acc) res
        res2 = merklePaths' a l (Left (treeHash r) : acc) res1

showMerklePath :: MerklePath -> String
showMerklePath = showMerklePath' False where
    showMerklePath' :: Bool -> MerklePath -> String
    showMerklePath' _ [] = ""
    showMerklePath' False ((Left h) : xs)  = "<" ++ showHash h ++ showMerklePath' True xs
    showMerklePath' False ((Right h) : xs) = ">" ++ showHash h ++ showMerklePath' True xs
    showMerklePath' True ((Left h) : xs)   = "<" ++ showHash h ++ showMerklePath' True xs
    showMerklePath' True ((Right h) : xs)  = ">" ++ showHash h ++ showMerklePath' True xs

{- | Merkle paths and proofs
>>> map showMerklePath  $ merklePaths 'i' $ buildTree "bitcoin"
["<0x5214666a<0x7400b6ff>0x00000062",">0x69f4387c<0x6e00ad98>0x0000006f"]

>>> buildProof 'i' $ buildTree "bitcoin"
Just (MerkleProof 'i' <0x5214666a<0x7400b6ff>0x00000062)

>>> buildProof 'e' $ buildTree "bitcoin"
Nothing
-}

verifyProof :: Hashable a => Hash -> MerkleProof a -> Bool
verifyProof h proof = h == hashMerkleProof proof where
    hashMerkleProof :: Hashable a => MerkleProof a -> Hash
    hashMerkleProof (MerkleProof a []) = hash '0'
    hashMerkleProof (MerkleProof a ((Left h) : []))  = hash (a, h)
    hashMerkleProof (MerkleProof a ((Right h) : [])) = hash (h, a)
    hashMerkleProof (MerkleProof a ((Left h) : xs))  = hash (hashMerkleProof (MerkleProof a xs), h)
    hashMerkleProof (MerkleProof a ((Right h) : xs)) = hash (h, hashMerkleProof (MerkleProof a xs))

{- | Verifying proofs
>>> let t = buildTree "bitcoin"
>>> let proof = buildProof 'i' t
>>> verifyProof (treeHash t) <$> proof
Just True
>>> verifyProof 0xbada55bb <$> proof
Just False
-}