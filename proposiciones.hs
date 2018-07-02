
-- ===========================================
-- ====          Tipos de datos           ====
-- ===========================================

type Var   = String  -- nombres de variables
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp
    deriving (Eq, Ord)


-- ===========================================
-- ====             Fórmulas              ====
-- ===========================================

f1 = Si (No (V "p")) (Si (V "p") (Y (V "q") (No (V "q"))))
f2 = Y (V "p") (Si (No (V "q")) (No (V "p")))
f3 = Y (Y (V "p") (V "q")) (O (No (V "q")) (V "r"))
f4 = V "z"
f5 = Y (V "p") (No (V "p"))


-- ===========================================
-- ====            Instancias             ====
-- ===========================================

instance Show FProp where
    show (V var)           = var
    show (No fun)          = "~(" ++ show fun ++ ")"
    show (Y prop1 prop2)   = "(" ++ show prop1 ++ ") /\\ (" ++ show prop1 ++ ")"
    show (O prop1 prop2)   = "(" ++ show prop1 ++ ") \\/ (" ++ show prop1 ++ ")"
    show (Si prop1 prop2)  = "(" ++ show prop1 ++ ") -> (" ++ show prop2 ++ ")"
    show (Sii prop1 prop2) = "(" ++ show prop1 ++ ") <-> (" ++ show prop1 ++ ")"

-- TODO: instancias de Eq y Ord

-- ===========================================
-- ====      Funciones principales        ====
-- ===========================================

-- Función envoltorio. Obtiene la lista completa de variables,
-- después las filtra eliminando las repetidas.
vars :: FProp -> [Var]
vars f = unique (getVars f)

-- Comprueba que, para cualquier combinación de valores posible, f siempre es True
tautologia :: FProp -> Bool
tautologia f = all (== True) [eval f vl | vl <- allPosibleValues (vars f)]

-- Comprueba que existe al menos una combinación de valores para la cual f es True
satisfactible :: FProp -> Bool
satisfactible f = True `elem` [eval f vl | vl <- allPosibleValues (vars f)]

-- Para todos los valores con los que f es cierta, g debe serlo también (f -> g)
consecuencia :: FProp -> FProp -> Bool
consecuencia f g = all (== True) [implies f g vl | vl <- allPosibleValues (unique (vars f ++ vars g))]

-- Para cualquier conjunto de valores, f y g deben tener el mismo resultado (f <-> g)
equivalente :: FProp -> FProp -> Bool
equivalente f g = all (== True) [equiv f g vl | vl <- allPosibleValues (unique (vars f ++ vars g))]

-- Devuelve una lista de pares (f, cs) siendo cs todas las funciones consecuencia de f
consecuencias :: [FProp] -> [(FProp, [FProp])]
consecuencias fs = [(f, cs) | f <- fs, let cs = [c | c <- fs, c /= f && consecuencia f c], not (null cs)]

-- TODO: Divide la lista fs en sublistas con todos sus elementos equivalentes entre sí
--equivalentes :: [FProp] -> [[FProp]]
--equivalentes fs = [fs]


-- ===========================================
-- ====       Funciones auxiliares        ====
-- ===========================================

-- Avanza recursivamente hasta encontrar las variables y las devuelve concatenadas
getVars :: FProp -> [Var]
getVars (V var)         = [var]
getVars (No fun)        = getVars fun
getVars (Y fun1 fun2)   = getVars fun1 ++ getVars fun2
getVars (O fun1 fun2)   = getVars fun1 ++ getVars fun2
getVars (Si fun1 fun2)  = getVars fun1 ++ getVars fun2
getVars (Sii fun1 fun2) = getVars fun1 ++ getVars fun2

-- Filtra una lista eliminando los elementos duplicados
-- Source: https://www.rosettacode.org/wiki/Remove_duplicate_elements#Haskell
unique :: Eq a => [a] -> [a]
unique []       = []
unique (x : xs) = x : unique (filter (x /=) xs)

-- Evalua una expresión en base a unos valores para sus variables
eval :: FProp -> [(Var, Bool)] -> Bool
eval (V var) ((x, y):xs) | var == x  = y
                         | otherwise = eval (V var) xs
eval (No prop) vl                    = not (eval prop vl)
eval (Y prop1 prop2) vl              = eval prop1 vl && eval prop2 vl
eval (O prop1 prop2) vl              = eval prop1 vl || eval prop2 vl
eval (Si prop1 prop2) vl             = implies prop1 prop2 vl
eval (Sii prop1 prop2) vl            = equiv prop1 prop2 vl

-- Transformación booleada de f -> g
implies :: FProp -> FProp -> [(Var, Bool)] -> Bool
implies f g vl = not (eval f vl) || eval g vl

-- Transformación booleana de f <-> g
equiv :: FProp -> FProp -> [(Var, Bool)] -> Bool
equiv f g vl = implies f g vl && implies g f vl

-- Genera todos los valores booleanos posibles para un conjunto de variables
-- Source: https://stackoverflow.com/a/29713381/7809508
allPosibleValues :: [Var] -> [[(Var, Bool)]]
allPosibleValues = foldr (\x xs -> (:) <$> [(x,True),(x,False)] <*> xs) [[]]