{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

-- from base:
import Data.Function     ( ($) )
import Data.Bool         ( Bool(True), (||), otherwise )
import Data.Ord          ( (<) )
import Data.Char         ( String )
import Data.List         ( (++) )
import Control.Monad     ( return, (>>=), fail
                         , (>>), liftM2
                         )
import Control.Exception ( IOException )
import Text.Show         ( show )
import System.IO         ( IO )

-- from MonadCatchIO-transformers:
import Control.Monad.CatchIO ( MonadCatchIO, catch )

-- from transformers:
import Control.Monad.Trans ( MonadIO, lift )

-- from safer-file-handles:
import System.IO.SaferFileHandles ( RegionT
                                  , runTopRegion
                                  , runRegionT
                                  , File
                                  , openFile
                                  , IOMode(ReadMode, WriteMode)
                                  , dup
                                  , hGetLine
                                  , hIsEOF
                                  , hPutStrLn
                                  , print
                                  )


--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

main = test1

hReport ∷ MonadIO m ⇒ String → m ()
hReport = print -- TODO: Should actually be: hPutStrLn stderr

test1 = runTopRegion $ do
          h1 ← openFile "fname1" ReadMode
          h2 ← openFile "fname1" ReadMode
          -- Can't allocate the handle outside the top region...
          -- h3 ← lift $ openFile "fname1" ReadMode
          -- There is no region two levels up
          -- h3 ← lift $ lift $ openFile "fname1" ReadMode
          l1 ← hGetLine h1
          return True
          -- Can't do that: r escapes
          -- return h2

-- multiple region test
test2 = runTopRegion $ do
          h1 ← openFile "fname1" ReadMode
          h3 ← runRegionT $ do
                 h2 ← openFile "fname2" ReadMode
                 h3 ← lift (openFile "fname3" ReadMode)
                 -- Can't allocate the handle outside the top region...
                 -- h4 ← lift $ lift $ openFile "fname1" ReadMode
                 l1 ← hGetLine h1
                 l1 ← hGetLine h2
                 l1 ← hGetLine h3
                 return h3 -- but this is OK: h3 assigned to the parent region
                 -- Can't do that: r escapes
                 -- return h2
          l1 ← hGetLine h1
          l1 ← hGetLine h3
          return l1

test2' fname = do
  h1 ← openFile fname ReadMode
  -- If this line is uncommented, test2'r reports an error.
  -- Indeed, test2' must then be used within another region rather than
  -- at the `top level'. The reported error clearly states the
  -- violation of the subtyping constraint: a child region computation
  -- cannot be coerced to the type of its ancestor
  -- h2 ← lift $ openFile fname ReadMode
  return ()
test2'r = runTopRegion (test2' "fname")

testmany ∷ IO String
testmany = runTopRegion $ do
             h1 ← openFile "fname1" ReadMode
             h5 ← runRegionT $ do
                    h2 ← openFile "fname2" ReadMode
                    runRegionT $ do
                      h3 ← openFile "fname3" ReadMode
                      runRegionT $ do
                        h4 ← openFile "fname4" ReadMode
                        l1 ← hGetLine h1
                        l2 ← hGetLine h2
                        l3 ← hGetLine h3
                        l4 ← hGetLine h4
                        h5 ← lift $ lift $ lift $
                               openFile "fname5" ReadMode
                        return h5
             hGetLine h5


-- An attempt to leak the computation.
-- Now, it won't work...
{-
test2' = runTopRegion $ do
           h1 ← openFile "fname1" ReadMode
           let c1 = hGetLine h1
           c1
           ac ← runRegionT $ do
                  h2 ← openFile "fname2" ReadMode
                  -- Fake the SIO type. Won't work though: h2 handle contaminates...
                  return ((hGetLine h2) `asTypeOf` c1)

           -- ac
           runRegionT $ do
             -- That too is a type error: lack of polymorphism in runRegionT
             -- ac
             return ()

           return True
-}



-- The above error is merely due to force monomorphism in the
-- monadic bind (do ac ← ...). One may think that a higher-rank type
-- may give us a way around the monomorphic binding in do, and
-- so to defeat the safety.
-- Fortunately, our approach prevents such a `way-around' and so
-- safety is preserved.
{-
newtype WC r1 = WC
    { unWC ∷ ∀ r2 . RegionT File r2 (RegionT File r1 IO) String }

test2'' = runTopRegion $ do
  h1 ← openFile "/dev/null" ReadMode
  ac ← runRegionT $ do
    h2 ← openFile "/dev/null" ReadMode
    -- Fake the IORT type. Won't work though... Good
    return $ WC $ hGetLine h2

  -- unWC ac
  runRegionT $ do
    -- If this were allowed, safety would have been defeated.
    -- Fortunately, we can't even construct the WC value:
    -- the type error is reported at `return (WC (hGetLine h2))'
    -- above.
    unWC ac
    return ()

  return True
-}



{- TODO: I don't support 'sNewIORef' yet.

-- Attempts to leak handles and computations via mutation
testref = runTopRegion (
    do
    h1 ← openFile "fname1" ReadMode
    rh ← sNewIORef undefined    -- a ref cell holding a handle
    let c1 = hGetLine h1
    c1
    ra ← sNewIORef undefined    -- a ref cell holding a computation
    runRegionT (do
         h2 ← openFile "fname2" ReadMode
         -- sWriteIORef rh h1
         -- sWriteIORef rh h2 -- type error, 's' of the inner region escapes
         -- sWriteIORef ra (hGetLine h1) -- OK
         -- sWriteIORef ra (lift (hGetLine h2))
         -- sWriteIORef ra (hGetLine h2) -- error: subtyping violation
         return ()
       )
    runRegionT (do
            -- sReadIORef ra >>= id
            return ()
           )
    return True
   )
-}

{- Ken's test:
A programming example using the enumerator (rather than cursor) pattern to
    (1) read a file name from a file
    (2) open that file and zip the two files' contents together
thus assuring that the files are accessed correctly and resources
disposed of completely.
-}

till condition iteration = loop where
  loop = do b ← condition
            if b then return () else iteration >> loop

test3 = runTopRegion $ do
          h1 ← openFile "/tmp/SafeHandles.hs" ReadMode
          h3 ← runRegionT $ test3_internal h1
          -- once we closed h2, we write the rest of h1 into h3
          till (hIsEOF h1)
               (hGetLine h1 >>= hPutStrLn h3)
          hReport "test3 done"

{- The following shows that we do not have to put all IO code in one big
function. We can spread it out.

The inferred type for the following is _region-polymorphic_:

test3_internal ∷ ∀ ioMode
                   s1 s2
                   (pr1 :: * -> *) (pr2 :: * -> *)
               . ( ReadModes ioMode
                 , MonadCatchIO pr1
                 , pr2 `ParentOf` (RegionT File s1 (RegionT File s2 pr1))
                 )
               ⇒ RegionalFileHandle ioMode pr2
               → RegionT File s1 (RegionT File s2 pr1)
                         (RegionalFileHandle W (RegionT File s2 pr1))
-}
test3_internal h1 = do
  h2 ← openFile "/tmp/ex-file.conf" ReadMode
  fname ← hGetLine h2           -- read the fname from the config file
  -- allocate handle in the parent region
  h3 ← lift $ openFile fname WriteMode
  -- zip h2 and h1 into h3
  hPutStrLn h3 fname
  till (liftM2 (||) (hIsEOF h2) (hIsEOF h1))
       (hGetLine h2 >>= hPutStrLn h3 >>
        hGetLine h1 >>= hPutStrLn h3)
  hReport "Finished zipping h1 and h2"
  return h3 -- but this is OK: h3 assigned to a parent region
  -- return h2 -- that would be an error: h2 can't escape

test4 h1 h2 = do
              d1 ← hGetLine h1
              hPutStrLn h2 d1

{-
Inferred type: region-polymorphic, as expected.
Also note the correctly inferred IOModes:
test4 ∷ ∀ readMode writeMode
          (pr1 :: * -> *) (pr2 :: * -> *)
          (cr :: * -> *)
      . ( pr1 `ParentOf` cr
        , pr2 `ParentOf` cr
        , ReadModes  readMode
        , WriteModes writeMode
        , MonadIO cr
        )
      ⇒ RegionalFileHandle readMode  pr1
      → RegionalFileHandle writeMode pr2
      → cr ()
-}

-- Testing for problems in opening a file
-- We copy the contents of fname_in into fname_out.
-- If fname_in does not exist, write a message to fname_out to that effect.
-- Nothing bad happens if the file could not be opened as
-- no file reference (safe handle) is created in that case.

test_copy fname_in fname_out = do
  hout ← openFile fname_out WriteMode
  (do runRegionT $ do
        hin ← openFile fname_in ReadMode
        till (hIsEOF hin)
             (hGetLine hin >>= hPutStrLn hout)
      hReport "Finished copying")
   `catch` \(e ∷ IOException) -> do
     hReport ("Exception caught: " ++ show e)
     hPutStrLn hout ("Copying failed: " ++ show e)

test_of1 = runTopRegion (test_copy "/etc/mtab" "/tmp/t1")
test_of2 = runTopRegion (test_copy "/non-existent" "/tmp/t1")

-- Implement this test by Ken:
{-
It's actually not clear to me, in the solution you propose, what happens
when we have three regions (call them P, Q, R, from oldest to youngest)
and we first dup a handle from R to Q and then dup the same handle from
R to P.  Would the region library code know at run time whether to
forward all three copies of the same handle to Q or to P?
-}

-- Dynamically extending the lifetime of handles
test_dup = runTopRegion $ do               -- Region P
  hq ← runRegionT $ do                     -- region Q
    hr ← runRegionT $ do                   -- region R
      h2  ← openFile "/etc/mtab" ReadMode
      _   ← dup h2 -- duplicates are OK
      h2' ← dup h2
      return h2'
    hGetLine hr
    hReport "Region Q finished"
    dup hr
  hGetLine hq
  hReport "Outer region finished"

-- Example suggested by Matthew Fluet

test5 = runTopRegion $ do
  h ← runRegionT $ test5_internal "/tmp/ex-file2.conf"
  l ← hGetLine h
  hReport $ "Continuing processing the older file, read: " ++ l
  hReport "test5 done"

test5_internal conf_fname = do
  hc ← openFile conf_fname ReadMode
  fname1 ← hGetLine hc  -- read the fname from the config file
  fname2 ← hGetLine hc  -- read the other fname from the config file
  h1 ← openFile fname1 ReadMode
  h2 ← openFile fname2 ReadMode
  l1 ← hGetLine h1
  l2 ← hGetLine h2
  hReport $ "read entries: " ++ show (l1,l2)
  let (fname_old, h_old) | l1 < l2   = (fname2, h2)
                         | otherwise = (fname1, h1)
  hReport ("Older log file: " ++ fname_old)
  dup h_old -- prolong the life of that handle

-- Issues with inferring region-polymorphic code
testp1 h = hGetLine h
-- testp1 ∷ ∀ ioMode (pr :: * -> *) (cr :: * -> *)
--        . ( pr `ParentOf` cr
--          , MonadIO cr
--          , ReadModes ioMode
--          )
--        ⇒ RegionalFileHandle ioMode pr
--        → cr String

-- The following, essentially equivalent, code however gives problem
-- testp2 h = runRegionT $ hGetLine h
-- Could not deduce (MonadRaise m1 (IORT s1 m)) from the context ()
-- And so does this
-- testp3 h = hGetLine h >> runRegionT (hGetLine h)

{- TODO: testp4 gives the following type error:

Ambiguous type variable `resource' in the constraint:
      `Control.Monad.Trans.Region.Internal.Resource resource'

-- But the following is OK:
testp4 h = runRegionT $ lift $ hGetLine h
{- inferred type is polymorphic as desired.
testp4 :: (RMonadIO m, MonadRaise m1 (IORT s m)) =>
          SHandle m1 -> IORT s m String
-}

-- usage example
testp4r = runTopRegion $ do
  h1 ← openFile "/etc/motd" ReadMode
  testp4 h1
-}


-- The End ---------------------------------------------------------------------
