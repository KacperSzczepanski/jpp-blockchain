--Kacper Szczepański ks418474

module PPrint where

writeln :: String -> IO ()
writeln = putStrLn

showsPair :: Show a => (String, a) -> ShowS
showsPair (k,v) = ((k ++ ": " ++ show v) ++)

pprH, pprV :: [ShowS] -> ShowS
pprV = intercalateS ("\n" ++)
pprH = intercalateS (" " ++)

intercalateS :: ShowS -> [ShowS] -> ShowS
intercalateS sep list = foldl (\acc s -> acc . s) id (separate list sep []) where
    separate :: [a] -> a -> [a] -> [a]
    separate [] _ res = res
    separate [x] _ res = x : res
    separate (x : xs) sep res = x : (sep : separate xs sep res)

pprListWith :: (a -> ShowS) -> [a] -> ShowS
pprListWith f list = pprV (map f list)

runShows :: ShowS -> IO ()
runShows = putStrLn . ($"")
