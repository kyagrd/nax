{-# LANGUAGE RankNTypes #-}

module Main where

-- to hide the 3.1.1 vwrsion of parsec, type at the cygwin prompt
-- ghc-pkg hide parsec-3.1.1

import qualified Control.Exception as Ex
import Control.Monad(foldM)
import Data.IORef(IORef)

import Text.PrettyPrint.HughesPJ(Doc,text,int,(<>),(<+>),($$),($+$)
                                ,render,vcat,sep,nest,parens)
import Text.ParserCombinators.Parsec.Pos(SourcePos,newPos)

import UniqInteger(resetnext,nextinteger)
import Names 
import Syntax   
import Parser 
import Value 
import Eval 
import Types(zonkRho,zonkScheme,zonkExp,zonk,zonkKind
            ,generalizeRho)
import TypeCheck(Frag(..),NameContents(..),addTable,elab,inferExpT,tvsEnv,nullFrag,wellFormedType,browseFrag)
import Monads(FIO,runFIO,handle,fio,Id(..),runId
             , writeln
             ,newRef,writeRef,readRef)
import Data.Char(isSpace)             

-------------------------------------------------------------------------

go = run "tests/data.nax"
work = run "tests/work.nax"

evalDecs :: [Decl TExpr] -> VEnv -> IO (VEnv)
evalDecs [] env = return env
evalDecs (d:ds) env = evalDecC env d (\ env2 -> evalDecs ds env2)

initialEnvs :: FIO (Frag, VEnv)
initialEnvs = 
      do { let acc (env,ds) d = do { (e2,d2) <- elab False env d; return(e2,d2:ds)}
               frag1 = nullFrag{values=rtSub}
               env1 = (foldr (\ ((n,uniq,v),(nm,sch)) e -> addTable EVAR (nm,Left(TEVar nm sch,sch)) e) frag1 smartPrims,[])
         ; (envTC,tdecls) <- foldM acc env1 decls
         ; fio (resetnext (index+1))
         ; envRT <- fio (evalDecs (reverse tdecls)  -- foldM acc, reverses list order
                                  (VEnv pairsRT rtSub))
         ; return(envTC,envRT) }
  where pairsRT = map fst smartPrims 
        rtSub = map f smartPrims
        f (x@(nm,n,v),typecheck) = (nm,Exp(CSP x))
        (nm,index,v) = last pairsRT
        decls = parseWithName "predefined" (layout decl (return ())) (unlines preDefinedDeclStrings)




checkEval :: IORef (Frag, VEnv) -> (Frag, VEnv) -> Decl Expr -> FIO (Frag, VEnv)
checkEval ref (tcEnv,rtEnv) d = 
  do { (tcEnv2,d2) <- elab True tcEnv d
     ; let doc = ppDecl (ppinfo tcEnv) ppTExpr d2
     ; writeln("\n\n"++render doc)
     ; rtEnv2 <- fio (evalDecC rtEnv d2 return)
     ; let ans = (tcEnv2{values=ctbindings rtEnv2},rtEnv2)
     ; writeRef ref ans
     ; return ans }
     
checkThenEvalOneAtATime ref [] envs = return envs
checkThenEvalOneAtATime ref (d:ds) envs = 
  do { envs2 <- checkEval ref envs d
     ; checkThenEvalOneAtATime ref ds envs2 }
        
loadProgram pi (Prog ds) = 
  do { (ce,re) <- initialEnvs
     ; let envs = (ce{ppinfo = pi},re)
     ; ref <- newRef envs
     ; let errF message = do { writeln message; readRef ref }
     ; handle  5 (checkThenEvalOneAtATime ref ds envs) errF
     ; readRef ref }


errF pos n message = error (show pos ++ message)

run name = runX pi0 name

runX pi name =
  do { let catch (Ex.ErrorCall s) = putStrLn s >> return(Prog [])
           handlers = [Ex.Handler catch]
     ; prog <- Ex.catches (parseFile program name) handlers
     -- ; putStrLn(show prog)
     ; (tcEnv,rtEnv) <- runFIO (loadProgram pi prog) errF
     ; putStrLn ("\nNax interpretor\n")
     ; loop2 name (tcEnv,rtEnv)
     }

loop2 :: String -> (Frag,VEnv) -> IO ()
loop2 path (envx@(frag,venv)) = Ex.catches 
   (do { putStr "nax> "
       -- ; putStrLn(plistf id "(" (map fst envx) "," ")")
       ; s <- getLine
       ; case s of
           (':' : '?' : _) ->
               putStrLn ("\n:q    Quit"++
                         "\n:b n  Browse n"++
                         "\n:r    Reload"++
                         "\n:t x  Type x"++
                         "\n:k x  Kind x"++
                         "\n:p x  Flip printing parameter x"++
                         "\n exp  Evaluate exp") >> loop2 path envx
           ":q" -> return ()
           (':' : 'b' : more) -> 
                 do { let tag = (dropWhite more)
                    ; putStrLn(browse tag venv)
                    ; putStrLn(browseFrag tag frag)
                    ; loop2 path envx }
           ":r" -> runX (ppinfo frag) path
           (':' : 't' : more) -> tCom envx more >> loop2 path envx
           (':' : 'k' : more) -> kCom envx more >> loop2 path envx
           (':' : 'p' : more) -> do { e <- pCom envx more; loop2 path e}
           "" -> loop2 path (envx)
           _  -> do { string <- action envx s
                    ; putStrLn string 
                    ; loop2 path (envx) }
       }) handlers
  where catchError (Ex.ErrorCall s) = putStrLn s >> loop2 path (envx)
        handlers = [Ex.Handler catchError]

-----------------------------------------------
-- control the printing environment

pCom (tcEnv,rtEnv) more =
  case dropWhile isSpace more of
    "In" -> return (adjust "In" tcEnv,rtEnv)
    "Mu" -> return (adjust "Mu" tcEnv,rtEnv)
    "Cast" -> return(adjust "Cast" tcEnv,rtEnv)
    "PatType" -> return(adjust "PatType" tcEnv,rtEnv)
    "" -> mapM f choices >> return (tcEnv,rtEnv)
    tag -> putStrLn("Unknown printng feature '"++ tag++"'") >> return (tcEnv,rtEnv)
  where choices = pChoices pi
        pi = ppinfo tcEnv
        f (x,t) = putStrLn("show "++x++" = "++show t)
        flip x [] = []
        flip x ((y,t):m) = if x==y then (x,not t): m else (y,t):flip x m
        adjust x tcEnv = tcEnv{ppinfo = pi{pChoices = flip x choices}}


-----------------------------------------------
kCom (tcEnv,rtEnv) more = 
  do { let mess = ["Computing the kind of the type:\n   "++more++"\nusing the :k command."]
           typ = (parse2 typP more)
     ; kind <- runFIO (do { (typ,kind) <- wellFormedType noPos mess tcEnv typ
                          ; zonkKind kind} ) errF
     ; putStrLn (show kind) }
     
----------------------------------------------
tCom (envx@(tcEnv,rtEnv)) more =
  do { pair@(sig,term) <- runFIO(checkType envx (parse2 expr more)) errF
     ; let pi = ppinfo tcEnv
     ; putStrLn(render(vcat[sep[text "The term"
                               ,parens(ppTExpr pi term)
                               ,text "has type:"]
                           ,ppScheme pi sig]))
     }

checkType :: (Frag, VEnv) -> Expr -> FIO(Scheme,TExpr)
checkType (tcEnv,rtEnv) exp = 
  do { (rho,exp2) <- inferExpT tcEnv exp
     ; r2 <- zonkRho rho
     ; free <- tvsEnv tcEnv
     ; (sch,vs) <- generalizeRho free r2
     ; sch2 <- zonkScheme sch
     ; exp3 <- zonkExp exp2
     ; return(sch2,exp3)}

action :: (Frag, VEnv) -> [Char] -> IO String
action (tcEnv,rtEnv) s = 
  do { let exp = (parse2 expr s)
     -- ; putStrLn("|"++show exp++"|")
     ; (sch,exp2) <- runFIO (checkType (tcEnv,rtEnv) exp) errF
     ; v <- evalC exp2 rtEnv return
     ; let pi = ppinfo tcEnv
     ; return (render(sep[sep[ppTExpr pi exp2<>text ":",ppScheme pi sch,text "="]
                         , nest 3 (ppValue pi  v)  {- $$ (text (showS sch)) -} 
                         ])) }

-----------------------------------------------------------------------
smartPrims = 
        [(injectIII "+"  2(+))
        ,(injectIII "-"  3(-))
        ,(injectIII "*"  4 (*))
        ,(injectIII "/"  5(div))
        ,(injectBBB "&&" 6(&&))
        ,(injectBBB "||" 7(||))
        ,(notInfo        8    )
        ,(injectBBB "=>" 9 imply)
        ,(injectIIB "<"  10(<))
        ,(injectIIB "<=" 11 (<=))
        ,(injectIIB ">=" 12 (>=))
        ,(injectIIB ">"  13 (>))
        ,(injectIIB "==" 14 (==))
        ,(injectIIB "/=" 15 (/=))
        ,((Nm("trace",preline 16),16,traceM 16),(Nm("trace",preline 16),traceScheme))
	,((Nm("show",preline 18),18,VFun whoknows (\ v -> to(show v))),(Nm("show",preline 18),showScheme))
        ,((Nm("reify",preline 19),19, reifyV 19),(Nm("reify",preline 19),reifyScheme))
        
        
        ]



traceM:: Integer -> Value IO   
traceM n = VFunM n (\ mess k -> (k(VFunM (n+1) (\ v k2 ->  putStrLn (show mess++" "++show v)>> k2 v))))

reifyV :: Integer -> Value IO
reifyV n = VFunM n (\ v k -> do { x <- reify Nothing v; k (VCode x)})
reifyScheme = Sch [(a,Type Star)] (Tau(arrT atyp (TyApp code atyp)))
  where a = toName "a"
        atyp = (TyVar a Star)
        code = TyCon None (toName "Code") (PolyK [] (Karr Star Star))


envIO = 
   [ ("trace",(traceM 0 ,traceScheme))
   , ("show",(VFun whoknows (\ v -> to(show v)),showScheme))
   , ("reify",(reifyV 1,reifyScheme))
   ] ++ prims
 

failT m a =  a `arrT` (TyApp m a)
failSch m a = Sch [(av,Type Star)] (Tau (failT m a))
 where (TyVar av k) = a

bindT m a b = (TyApp m a) `arrT` ((a `arrT` (TyApp m b)) `arrT` (TyApp m b))
bindSch m a b = Sch [(av,Type Star),(bv,Type Star)] (Tau (bindT m a b))
  where (TyVar av _) = a  
        (TyVar bv _) = b
       

returnSch m a = Sch [(av,Type Star)] (Tau (returnT m a))
  where (TyVar av k) = a
        returnT m a = a `arrT` (TyApp m a)


          
------------------------------------------

class Monad m => Comp m where
  println:: String -> m()
  next:: m Integer 
  mkFun :: 
     Integer -> 
     (forall a. Value m -> (Value m -> m a) -> m a) ->
     (Value m -> m b) ->
     m b

instance Comp Id where
  println s = return ()
  next = return 0
  mkFun n f k = k(VFun whoknows (\ v -> runId(f v return)))  -- use pure functions in the Id monad

instance Comp IO where
  println = putStrLn
  next = nextinteger
  mkFun n f k = k(VFunM n f)
  

 
{-
testdata = run "AlgData.funlog"
testsoduko = run "Soduko.funlog"
testfun = run "Functions.funlog"
teste = run "empty.funlog"
testform = run "formula.funlog"




-}     