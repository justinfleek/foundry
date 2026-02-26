{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // foundry // core // text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Text
Description : Text utilities following Hydrogen Show debug convention
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Text conversion utilities that follow the Hydrogen Show debug convention.

== The Show Debug Convention

In Hydrogen (and by extension, foundry), the 'Show' type class serves as
**structured debugging infrastructure**, not mere pretty-printing.

Every type implements Show in a way that enables:

  1. Runtime introspection — Agents can inspect values programmatically
  2. Debug feature flags — Conditional debug output without recompilation
  3. Graph visualization — Co-effect/effect edges become inspectable
  4. Deterministic logging — Same value = same string = reproducible debugging

== Show Output Format

Show output should be parseable and unambiguous:

@
(TypeName field1:value1 field2:value2)
@

Examples:

@
(Point2D 100.0 50.0)
(Box3 min:(Vec3 1.0 2.0 3.0) max:(Vec3 4.0 5.0 6.0))
(BrandColor role:Primary oklch:(OKLCH 0.65 0.25 280.0))
@

See: hydrogen/docs/SHOW_DEBUG_CONVENTION.md
See: hydrogen/docs/SHOW_WORKFLOW.md

== Dependencies

Requires: text
Required by: All foundry packages that need Show → Text conversion

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Text
  ( -- * Show to Text Conversion
    tshow
  , tshowList
  
    -- * ByteString Conversion
  , bshow
  ) where

import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BC
import Data.Text (Text)
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Show to Text Conversion
--------------------------------------------------------------------------------

-- | Convert any Show instance to Text
--
-- This is the canonical way to convert Show output to Text in foundry.
-- The function is simple by design — the complexity should be in the
-- Show instances themselves, which must follow the Hydrogen convention.
--
-- == Usage
--
-- @
-- tshow (42 :: Int)        -- "42"
-- tshow (OKLCH 0.65 0.25 280.0)  -- "(OKLCH 0.65 0.25 280.0)"
-- tshow [1,2,3]            -- "[1,2,3]"
-- @
--
-- == Why T.pack . show?
--
-- This is intentionally simple. Alternatives like lazy text builders or
-- string interpolation add complexity without benefit. The Show instance
-- does the formatting work; we just convert the result.
--
-- For performance-critical paths with many conversions, consider:
--   1. Using ByteString directly (bshow)
--   2. Building Text with a Text.Builder
--   3. Caching Show output for immutable values
--
tshow :: Show a => a -> Text
tshow = T.pack . show

-- | Convert a list to Text with custom separator
--
-- @
-- tshowList ", " [1,2,3]  -- "1, 2, 3"
-- tshowList " " ["a","b"]  -- "\"a\" \"b\""
-- @
--
tshowList :: Show a => Text -> [a] -> Text
tshowList sep = T.intercalate sep . map tshow

--------------------------------------------------------------------------------
-- ByteString Conversion
--------------------------------------------------------------------------------

-- | Convert any Show instance to ByteString (Char8)
--
-- For contexts where ByteString is preferred over Text (e.g., hashing,
-- binary protocols, performance-critical logging).
--
-- Note: Uses Char8 encoding, so only safe for ASCII Show output.
-- Most Show instances produce ASCII, but be aware of this limitation.
--
-- @
-- bshow (42 :: Int)  -- "42"
-- bshow digest       -- hex string representation
-- @
--
bshow :: Show a => a -> ByteString
bshow = BC.pack . show
