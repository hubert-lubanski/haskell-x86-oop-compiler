module Common where
-- Kolorowe wyjście --
defaultColor :: String
defaultColor        = "\ESC[0m"
blackColor :: [Char] -> [Char]
blackColor str = _blackColor ++ str ++ defaultColor
_blackColor :: String
_blackColor          = "\ESC[30m"
redColor :: [Char] -> [Char]
redColor str = _redColor ++ str ++ defaultColor
_redColor :: String
_redColor            = "\ESC[31m"
greenColor :: [Char] -> [Char]
greenColor str = _greenColor ++ str ++ defaultColor
_greenColor :: String
_greenColor          = "\ESC[32m"
yellowColor :: [Char] -> [Char]
yellowColor str = _yellowColor ++ str ++ defaultColor
_yellowColor :: String
_yellowColor         = "\ESC[33m"
blueColor :: [Char] -> [Char]
blueColor str = _blueColor ++ str ++ defaultColor
_blueColor :: String
_blueColor           = "\ESC[34m"
magentaColor :: [Char] -> [Char]
magentaColor str = _magentaColor ++ str ++ defaultColor
_magentaColor :: String
_magentaColor        = "\ESC[35m"
cyanColor :: [Char] -> [Char]
cyanColor str = _cyanColor ++ str ++ defaultColor
_cyanColor :: String
_cyanColor           = "\ESC[36m"
whiteColor :: [Char] -> [Char]
whiteColor str = _whiteColor ++ str ++ defaultColor
_whiteColor :: String
_whiteColor          = "\ESC[37m"
altblackColor :: [Char] -> [Char]
altblackColor str = _altblackColor ++ str ++ defaultColor
_altblackColor :: String
_altblackColor       = "\ESC[90m"
altredColor :: [Char] -> [Char]
altredColor str = _altredColor ++ str ++ defaultColor
_altredColor :: String
_altredColor         = "\ESC[91m"
altgreenColor :: [Char] -> [Char]
altgreenColor str = _altgreenColor ++ str ++ defaultColor
_altgreenColor :: String
_altgreenColor       = "\ESC[92m"
altyellowColor :: [Char] -> [Char]
altyellowColor str = _altyellowColor ++ str ++ defaultColor
_altyellowColor :: String
_altyellowColor      = "\ESC[93m"
altblueColor :: [Char] -> [Char]
altblueColor str = _altblueColor ++ str ++ defaultColor
_altblueColor :: String
_altblueColor        = "\ESC[94m"
altmagentaColor :: [Char] -> [Char]
altmagentaColor str = _altmagentaColor ++ str ++ defaultColor
_altmagentaColor :: String
_altmagentaColor     = "\ESC[95m"
altcyanColor :: [Char] -> [Char]
altcyanColor str = _altcyanColor ++ str ++ defaultColor
_altcyanColor :: String
_altcyanColor        = "\ESC[96m"
altwhiteColor :: [Char] -> [Char]
altwhiteColor str = _altwhiteColor ++ str ++ defaultColor
_altwhiteColor :: String
_altwhiteColor       = "\ESC[97m"


appendAt :: Int -> String -> String -> String
appendAt col start what =
    let diff = col - (length . init . tail . show) start  in
    if diff <= 0 then start ++ what
    else
        start ++ replicate diff ' ' ++ what


caseBetween :: Ord a => a -> a -> a -> Bool
caseBetween lo hi x = lo <= x && x <= hi

caseRange :: (Foldable t, Eq a) => t a -> a -> Bool
caseRange range x = x `elem` range
