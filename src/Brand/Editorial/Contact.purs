-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // brand // editorial // contact
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Contact information formatting: phone formats, time formats, and
-- | contact format rules.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Editorial (main editorial module)

module Hydrogen.Schema.Brand.Editorial.Contact
  ( -- * Phone Format
    PhoneFormat
      ( PhoneHyphens
      , PhoneDots
      , PhoneSpaces
      , PhoneParensArea
      )
  , phoneFormatToString
  , parsePhoneFormat
  
  -- * Time Format
  , HourFormat
      ( Hour12
      , Hour24
      )
  , hourFormatToString
  , parseHourFormat
  
  , TimeFormat
  , mkTimeFormat
  , timeHourFormat
  , timeAmPmSpaced
  , timeRangeSeparator
  , timeMidnightConvention
  , timeNoonConvention
  
  -- * Contact Format Rules
  , ContactFormatRules
  , mkContactFormatRules
  , contactPhoneFormat
  , contactTimeFormat
  , contactAbbreviateDays
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (&&)
  , show
  , compare
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // phone format
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Phone number formatting style.
data PhoneFormat
  = PhoneHyphens      -- 555-123-4567
  | PhoneDots         -- 555.123.4567
  | PhoneSpaces       -- 555 123 4567
  | PhoneParensArea   -- (555) 123-4567

derive instance eqPhoneFormat :: Eq PhoneFormat

instance ordPhoneFormat :: Ord PhoneFormat where
  compare p1 p2 = compare (phoneToInt p1) (phoneToInt p2)
    where
      phoneToInt :: PhoneFormat -> Int
      phoneToInt PhoneHyphens = 0
      phoneToInt PhoneDots = 1
      phoneToInt PhoneSpaces = 2
      phoneToInt PhoneParensArea = 3

instance showPhoneFormat :: Show PhoneFormat where
  show = phoneFormatToString

-- | Convert phone format to string.
phoneFormatToString :: PhoneFormat -> String
phoneFormatToString PhoneHyphens = "hyphens"
phoneFormatToString PhoneDots = "dots"
phoneFormatToString PhoneSpaces = "spaces"
phoneFormatToString PhoneParensArea = "parentheses"

-- | Parse phone format from string.
parsePhoneFormat :: String -> Maybe PhoneFormat
parsePhoneFormat s = case String.toLower s of
  "hyphens" -> Just PhoneHyphens
  "hyphen" -> Just PhoneHyphens
  "dashes" -> Just PhoneHyphens
  "dots" -> Just PhoneDots
  "periods" -> Just PhoneDots
  "spaces" -> Just PhoneSpaces
  "space" -> Just PhoneSpaces
  "parentheses" -> Just PhoneParensArea
  "parens" -> Just PhoneParensArea
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // time format
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Hour display format.
data HourFormat
  = Hour12    -- 12-hour with AM/PM
  | Hour24    -- 24-hour (military)

derive instance eqHourFormat :: Eq HourFormat

instance ordHourFormat :: Ord HourFormat where
  compare h1 h2 = compare (hourToInt h1) (hourToInt h2)
    where
      hourToInt :: HourFormat -> Int
      hourToInt Hour12 = 0
      hourToInt Hour24 = 1

instance showHourFormat :: Show HourFormat where
  show = hourFormatToString

-- | Convert hour format to string.
hourFormatToString :: HourFormat -> String
hourFormatToString Hour12 = "12-hour"
hourFormatToString Hour24 = "24-hour"

-- | Parse hour format from string.
parseHourFormat :: String -> Maybe HourFormat
parseHourFormat s = case String.toLower s of
  "12-hour" -> Just Hour12
  "12" -> Just Hour12
  "am/pm" -> Just Hour12
  "24-hour" -> Just Hour24
  "24" -> Just Hour24
  "military" -> Just Hour24
  _ -> Nothing

-- | Time display rules.
type TimeFormat =
  { hourFormat :: HourFormat
  , amPmSpaced :: Boolean        -- Space before AM/PM (e.g., "5:00 PM" vs "5:00PM")
  , rangeSeparator :: String     -- e.g., "–" (en-dash), "-", "to"
  , midnightConvention :: String -- e.g., "12:00 AM", "midnight", "00:00"
  , noonConvention :: String     -- e.g., "12:00 PM", "noon"
  }

-- | Create time format rules.
mkTimeFormat 
  :: HourFormat 
  -> Boolean 
  -> String 
  -> String 
  -> String 
  -> Maybe TimeFormat
mkTimeFormat hf spaced rangeSep midnight noon =
  if String.length rangeSep >= 1 
     && String.length midnight >= 1 
     && String.length noon >= 1
    then Just
      { hourFormat: hf
      , amPmSpaced: spaced
      , rangeSeparator: rangeSep
      , midnightConvention: midnight
      , noonConvention: noon
      }
    else Nothing

-- | Get hour format.
timeHourFormat :: TimeFormat -> HourFormat
timeHourFormat tf = tf.hourFormat

-- | Check if AM/PM spaced.
timeAmPmSpaced :: TimeFormat -> Boolean
timeAmPmSpaced tf = tf.amPmSpaced

-- | Get range separator.
timeRangeSeparator :: TimeFormat -> String
timeRangeSeparator tf = tf.rangeSeparator

-- | Get midnight convention.
timeMidnightConvention :: TimeFormat -> String
timeMidnightConvention tf = tf.midnightConvention

-- | Get noon convention.
timeNoonConvention :: TimeFormat -> String
timeNoonConvention tf = tf.noonConvention

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // contact format rules
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Contact information formatting rules.
type ContactFormatRules =
  { phoneFormat :: PhoneFormat
  , timeFormat :: TimeFormat
  , abbreviateDays :: Boolean    -- e.g., "Mon" vs "Monday"
  }

-- | Create contact format rules.
mkContactFormatRules 
  :: PhoneFormat 
  -> TimeFormat 
  -> Boolean 
  -> ContactFormatRules
mkContactFormatRules pf tf abbrevDays =
  { phoneFormat: pf
  , timeFormat: tf
  , abbreviateDays: abbrevDays
  }

-- | Get phone format.
contactPhoneFormat :: ContactFormatRules -> PhoneFormat
contactPhoneFormat cfr = cfr.phoneFormat

-- | Get time format.
contactTimeFormat :: ContactFormatRules -> TimeFormat
contactTimeFormat cfr = cfr.timeFormat

-- | Check if days abbreviated.
contactAbbreviateDays :: ContactFormatRules -> Boolean
contactAbbreviateDays cfr = cfr.abbreviateDays
