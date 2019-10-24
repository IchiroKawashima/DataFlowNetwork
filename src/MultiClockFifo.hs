module MultiClockFifo where

import           Clash.Explicit.Prelude
import           Clash.Prelude                  ( mux )
import           Data.Maybe                     ( isJust )
import           Data.Constraint                ( Dict(..)
                                                , (:-)(Sub)
                                                )
import           Data.Constraint.Nat            ( leTrans )

fifoMem wclk rclk en addrSize@SNat full raddr writeM = asyncRam
    wclk
    rclk
    en
    (pow2SNat addrSize)
    raddr
    (mux full (pure Nothing) writeM)

ptrCompareT
    :: SNat addrSize
    -> (BitVector (addrSize + 1) -> BitVector (addrSize + 1) -> Bool)
    -> (BitVector (addrSize + 1), BitVector (addrSize + 1), Bool)
    -> (BitVector (addrSize + 1), Bool)
    -> ( (BitVector (addrSize + 1), BitVector (addrSize + 1), Bool)
       , (Bool, BitVector addrSize, BitVector (addrSize + 1))
       )
ptrCompareT addrSize@SNat flagGen (bin, ptr, flag) (s_ptr, inc) =
    ((bin', ptr', flag'), (flag, addr, ptr))
  where
  -- GRAYSTYLE2 pointer
    bin'  = bin + boolToBV (inc && not flag)
    ptr'  = (bin' `shiftR` 1) `xor` bin'
    addr  = truncateB bin

    flag' = flagGen ptr' s_ptr

-- FIFO empty: when next pntr == synchronized wptr or on reset
isEmpty = (==)
rptrEmptyInit = (0, 0, True)

-- FIFO full: when next pntr == synchronized {~wptr[addrSize:addrSize-1],wptr[addrSize-2:0]}
isFull
    :: forall addrSize
     . (2 <= addrSize)
    => SNat addrSize
    -> BitVector (addrSize + 1)
    -> BitVector (addrSize + 1)
    -> Bool
isFull addrSize@SNat ptr s_ptr = case leTrans @1 @2 @addrSize of
    Sub Dict ->
        let
            a1 = SNat @(addrSize - 1)
            a2 = SNat @(addrSize - 2)
        in
            ptr == (complement (slice addrSize a1 s_ptr) ++# slice a2 d0 s_ptr)

wptrFullInit = (0, 0, False)

-- Dual flip-flop synchronizer
ptrSync clk1 clk2 rst2 =
    register clk2 rst2 0 . register clk2 rst2 0 . unsafeSynchronizer clk1 clk2

-- Async FIFO synchronizer
asyncFIFOSynchronizer
    :: (KnownDomain wdom, KnownDomain rdom, 2 <= addrSize)
    => SNat addrSize
  -- ^ Size of the internally used addresses, the  FIFO contains 2^addrSize
  -- elements.
    -> Clock wdom
  -- ^ Clock to which the write port is synchronized
    -> Clock rdom
  -- ^ Clock to which the read port is synchronized
    -> Reset wdom
    -> Reset rdom
    -> Enable wdom
    -> Enable rdom
    -> Signal rdom Bool
  -- ^ Read request
    -> Signal wdom (Maybe a)
  -- ^ Element to insert
    -> ( Signal rdom a
       , Signal rdom Bool
       , Signal wdom Bool
       )
  -- ^ (Oldest element in the FIFO, empty flag, full flag)
asyncFIFOSynchronizer addrSize@SNat wclk rclk wrst rrst wen ren rinc wdataM =
    (rdata, rempty, wfull)
  where
    s_rptr = dualFlipFlopSynchronizer rclk wclk wrst wen 0 rptr
    s_wptr = dualFlipFlopSynchronizer wclk rclk rrst ren 0 wptr

    rdata  = fifoMem wclk
                     rclk
                     wen
                     addrSize
                     wfull
                     raddr
                     (liftA2 (,) <$> (pure <$> waddr) <*> wdataM)

    (rempty, raddr, rptr) = mealyB rclk
                                   rrst
                                   ren
                                   (ptrCompareT addrSize (==))
                                   (0, 0, True)
                                   (s_wptr, rinc)

    (wfull, waddr, wptr) = mealyB wclk
                                  wrst
                                  wen
                                  (ptrCompareT addrSize (isFull addrSize))
                                  (0, 0, False)
                                  (s_rptr, isJust <$> wdataM)
