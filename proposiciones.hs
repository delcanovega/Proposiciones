
-- ===========================================
-- ====          Tipos de datos           ====
-- ===========================================

type Var   = String  -- nombres de variables
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp


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

-- Igualdad estructural excepto en las operaciones /\ y \/,
-- en las cuales el orden de los operandos no importa
instance Eq FProp where
    (V var1) == (V var2)                   = var1 == var2
    (No prop1) == (No prop2)               = prop1 == prop2
    (Y prop1 prop2) == (Y prop3 prop4)     = (prop1 == prop3 && prop2 == prop4) ||
                                             (prop1 == prop4 && prop2 == prop3)
    (O prop1 prop2) == (O prop3 prop4)     = (prop1 == prop3 && prop2 == prop4) ||
                                             (prop1 == prop4 && prop2 == prop3)
    (Si prop1 prop2) == (Si prop3 prop4)   = prop1 == prop3 && prop2 == prop4
    (Sii prop1 prop2) == (Sii prop3 prop4) = prop1 == prop3 && prop2 == prop4

-- Cuidado con el orden: a será menor que b si b -> a
instance Ord FProp where
    a <= b = consecuencia b a

instance Show FProp where
    show (V var)           = var
    show (No fun)          = "~(" ++ show fun ++ ")"
    show (Y prop1 prop2)   = "(" ++ show prop1 ++ ") /\\ (" ++ show prop1 ++ ")"
    show (O prop1 prop2)   = "(" ++ show prop1 ++ ") \\/ (" ++ show prop1 ++ ")"
    show (Si prop1 prop2)  = "(" ++ show prop1 ++ ") -> (" ++ show prop2 ++ ")"
    show (Sii prop1 prop2) = "(" ++ show prop1 ++ ") <-> (" ++ show prop1 ++ ")"

-- ===========================================
-- ====      Funciones principales        ====
-- ===========================================

-- Obtiene una lista con las distintas variables que contiene la fórmula
-- · Primero obtiene la lista completa de variables (puede haber repeticiones)
-- · Después las filtra eliminando las repetidas.
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

-- Divide la lista fs en sublistas con todos sus elementos equivalentes entre sí
-- · Para ello primero crea tantas listas de funciones equivalentes como funciones reciba,
-- por ello si f y g son equivalentes ambas apareceran tanto en la lista de f como en la lista de g
-- · Por último se eliminan los elementos repetidos de esta lista de listas,
-- es decir, aquellas listas que ya tenemos de forma idéntica.
equivalentes :: [FProp] -> [[FProp]]
equivalentes fs = unique [[e | e <- fs, equivalente f e] | f <- fs]


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


-- ===========================================
-- ====        Parte opcional: I/O        ====
-- ===========================================

main :: IO()
main = do
    putStrLn "Bienvenido al programa de evaluación de fórmulas lógicas v1.5"
    
    putStrLn "Menú:"
    putStrLn "  1 - Información de uso"
    putStrLn "  2 - Evaluación de fórmulas"
    putStrLn "  0 - Salir"

    putStr ">> "
    n <- getLine
    if n == "0" then do
        putStrLn "¡Hasta la próxima!"
        return ()

    else if n == "1" then do
        putStrLn "Las operaciones que podrás realizar dependerán del número de fórmulas:"
        putStrLn "  · Si introduces una: comprobar si es satisfactible, si se trata de una tautología o consultar su lista de variables"
        putStrLn "  · Si introduces dos: comprobar si una es consecuencia de la otra o si son equivalentes"
        putStrLn "  · Si introduces más de dos: consultar las consecuencias de cada una de ellas o dividirlas en particiones de funciones equivalentes"
        putStrLn "  · Si no introduces ninguna fórmula el programa finalizará"
        putStrLn "Cada fórmula deberá ir en una línea y tendrán la forma ~p \\/ (p -> (q /\\ ~q))"
        putStrLn "Introduce 0 cuando hayas acabado"

    else if n == "2" then do
        -- TODO: crear una lista vacía
        let fs = []
        -- TODO: leer una linea y parsearla a FProp
        putStrLn "Introduce tu fórmula:"
        f <- myReadLine
        parseLine f fs
        -- TODO: añadirla a la lista y volver al paso 1

        -- TODO: cuando se introduzca 0 mostrar operaciones disponibles en función de la longitud de la lista
        putStrLn "WIP"

    else
        putStrLn "Entrada no válida, finalizando programa"

myReadLine :: IO String
myReadLine = do
    putStr ">>"
    f <- getLine
    return (f)


parseLine :: String -> [FProp] -> [FProp]
parseLine f fs
    | head f == 0 = fs
    | head f == V = V tail f : fs