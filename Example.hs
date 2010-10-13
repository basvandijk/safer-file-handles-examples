{-# LANGUAGE UnicodeSyntax
           , RankNTypes
           , KindSignatures
           , ScopedTypeVariables
           , FlexibleContexts
  #-}

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

-- from base:
import Prelude                    ( undefined, fromInteger, id )
import Data.Function              ( ($), (.), flip )
import Data.Bool                  ( Bool(True), (||), otherwise )
import Data.Ord                   ( (<) )
import Data.Char                  ( String )
import Data.List                  ( (++), map )
import Data.IORef                 ( newIORef, writeIORef, readIORef )
import Control.Monad              ( return, (>>=), fail, (>>), liftM2 )
import Control.Exception          ( IOException )
import Control.Concurrent         ( threadDelay )
import Text.Show                  ( show )
import System.IO                  ( IO )

-- from MonadCatchIO-transformers:
import Control.Monad.CatchIO      ( MonadCatchIO, catch )

-- from transformers:
import Control.Monad.Trans.Class  ( lift )
import Control.Monad.IO.Class     ( MonadIO, liftIO )

-- from pathtype:
import System.Path                ( RelFile, asRelFile, asAbsFile )

-- from regions:
import Control.Monad.Trans.Region.Concurrent ( forkIOTopRegion )

-- from safer-file-handles:
import System.IO.SaferFileHandles


--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

main ∷ IO ()
main = testThread

-- inferred type:
-- hReport :: (AncestorRegion cr cr) => String -> cr ()
hReport s = stderr >>= flip hPutStrLn s

fname1, fname2, fname3, fname4, fname5 ∷ RelFile
[fname1, fname2, fname3, fname4, fname5] =
    map asRelFile $ map (("fname" ++) . show) [1..5]

test1 = runTopRegion $ do
          h1 ← openFile fname1 ReadMode
          h2 ← openFile fname1 ReadMode
          -- Can't allocate the handle outside the top region...
          -- h3 ← lift $ openFile fname1 ReadMode
          -- There is no region two levels up
          -- h3 ← lift $ lift $ openFile fname1 ReadMode
          l1 ← hGetLine h1
          return True
          -- Can't do that: r escapes
          -- return h2

-- multiple region test
test2 = runTopRegion $ do
          h1 ← openFile fname1 ReadMode
          h3 ← runRegionT $ do
                 h2 ← openFile fname2 ReadMode
                 h3 ← lift (openFile fname3 ReadMode)
                 -- Can't allocate the handle outside the top region...
                 -- h4 ← lift $ lift $ openFile fname1 ReadMode
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
test2'r = runTopRegion $ test2' fname1

testmany ∷ IO String
testmany = runTopRegion $ do
             h1 ← openFile fname1 ReadMode
             h5 ← runRegionT $ do
                    h2 ← openFile fname2 ReadMode
                    runRegionT $ do
                      h3 ← openFile fname3 ReadMode
                      runRegionT $ do
                        h4 ← openFile fname4 ReadMode
                        l1 ← hGetLine h1
                        l2 ← hGetLine h2
                        l3 ← hGetLine h3
                        l4 ← hGetLine h4
                        h5 ← lift $ lift $ lift $
                               openFile fname5 ReadMode
                        return h5
             hGetLine h5

-- An attempt to leak the computation.
-- Now, it won't work...
{-
test2'' = runTopRegion $ do
            h1 ← openFile fname1 ReadMode
            let c1 = hGetLine h1
            c1
            ac ← runRegionT $ do
                   h2 ← openFile fname2 ReadMode
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
    { unWC ∷ ∀ r2 . RegionT r2 (RegionT r1 IO) String }

test2''' = runTopRegion $ do
  h1 ← openFile (asAbsFile "/dev/null") ReadMode
  ac ← runRegionT $ do
    h2 ← openFile (asAbsFile "/dev/null") ReadMode
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

-- Attempts to leak handles and computations via mutation
testref = runTopRegion $ do
            h1 ← openFile fname1 ReadMode
            rh ← liftIO $ newIORef undefined    -- a ref cell holding a handle
            let c1 = hGetLine h1
            c1
            ra ← liftIO $ newIORef undefined    -- a ref cell holding a computation
            runRegionT $ do
              h2 ← openFile fname2 ReadMode

              liftIO $ writeIORef rh h1

              -- liftIO $ writeIORef rh h2 -- type error, 's' of the inner region escapes

              -- ok to exec the content of ra in the parent or in another sub-region
              -- of the parent region
              liftIO $ writeIORef ra (hGetLine h1)

              -- not ok: must not do anything with h2 outside this region
              -- liftIO $ writeIORef ra (lift (hGetLine h2))  -- error: subtyping violation

              -- liftIO $ writeIORef ra (hGetLine h2) -- error: subtyping violation
              return ()

            a <- liftIO $ readIORef ra
            a

            runRegionT $ do
              a <- liftIO $ readIORef ra
              lift a
              return ()

            return True

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
          h1 ← openFile (asAbsFile "/tmp/SafeHandles.hs") ReadMode
          h3 ← runRegionT $ test3_internal h1
          -- once we closed h2, we write the rest of h1 into h3
          till (hIsEOF h1)
               (hGetLine h1 >>= hPutStrLn h3)
          hReport "test3 done"

{- The following shows that we do not have to put all IO code in one big
function. We can spread it out.

The inferred type for the following is _region-polymorphic_:
-}
test3_internal ∷ ∀ ioMode
                   s1 s2
                   (pr1 ∷ * → *) (pr2 ∷ * → *)
               . ( ReadModes ioMode
                 , MonadCatchIO pr1
                 , pr2 `AncestorRegion` (RegionT s1 (RegionT s2 pr1))
                 )
               ⇒ RegionalFileHandle ioMode pr2
               → RegionT s1 (RegionT s2 pr1)
                   (RegionalFileHandle WriteMode (RegionT s2 pr1))
test3_internal h1 = do
  h2 ← openFile (asAbsFile "/tmp/ex-file.conf") ReadMode
  fname ← hGetLine h2           -- read the fname from the config file
  -- allocate handle in the parent region
  h3 ← lift $ openFile (asAbsFile fname) WriteMode
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
          (pr1 ∷ * → *) (pr2 ∷ * → *)
          (cr ∷ * → *)
      . ( pr1 `AncestorRegion` cr
        , pr2 `AncestorRegion` cr
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

test_of1 = runTopRegion (test_copy (asAbsFile "/etc/mtab")     (asAbsFile "/tmp/t1"))
test_of2 = runTopRegion (test_copy (asAbsFile "/non-existent") (asAbsFile "/tmp/t1"))

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
      h2  ← openFile (asAbsFile "/etc/mtab") ReadMode
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
  h ← runRegionT $ test5_internal (asAbsFile "/tmp/ex-file2.conf")
  l ← hGetLine h
  hReport $ "Continuing processing the older file, read: " ++ l
  hReport "test5 done"

test5_internal conf_fname = do
  hc ← openFile conf_fname ReadMode
  fname1 ← hGetLine hc  -- read the fname from the config file
  fname2 ← hGetLine hc  -- read the other fname from the config file
  h1 ← openFile (asAbsFile fname1) ReadMode
  h2 ← openFile (asAbsFile fname2) ReadMode
  l1 ← hGetLine h1
  l2 ← hGetLine h2
  hReport $ "read entries: " ++ show (l1,l2)
  let (fname_old, h_old) | l1 < l2   = (fname2, h2)
                         | otherwise = (fname1, h1)
  hReport ("Older log file: " ++ fname_old)
  dup h_old -- prolong the life of that handle

-- Issues with inferring region-polymorphic code
testp1 h = hGetLine h
-- inferred type:
-- testp1 :: (AncestorRegion pr cr, MonadIO cr, ReadModes ioMode)
--        => RegionalFileHandle ioMode pr -> cr String

-- The following, essentially equivalent, code however gives problem
-- testp2 h = runRegionT $ hGetLine h
-- Could not deduce (MonadRaise m1 (IORT s1 m)) from the context ()
-- And so does this
-- testp3 h = hGetLine h >> runRegionT (hGetLine h)

-- But the following is OK:
testp4 h = runRegionT $ lift $ hGetLine h

-- inferred type is polymorphic as desired:
-- testp4 :: (MonadCatchIO m, AncestorRegion pr m, ReadModes ioMode)
--        => RegionalFileHandle ioMode pr -> m String

-- usage example
testp4r = runTopRegion $ do
  h1 <- openFile (asAbsFile "/etc/motd") ReadMode
  testp4 h1

testThread = runTopRegion $ do
  h1 ← openFile fname1 ReadMode
  h2 ← openFile fname2 ReadWriteMode
  h3 ← openFile fname3 WriteMode

  tId1 ← forkIOTopRegion $ do
    liftIO $ threadDelay 1000000
    s ← hGetLine h1
    hPutStrLn h2 s
    putStrLn "Terminating thread 1."

  tId2 ← forkIOTopRegion $ do
    liftIO $ threadDelay 2000000
    hSeek h2 AbsoluteSeek 0
    s ← hGetLine h2
    hPutStrLn h3 s
    putStrLn "Terminating thread 2."

  liftIO $ threadDelay 3000000
  putStrLn "Terminating main thread."


-- The End ---------------------------------------------------------------------

