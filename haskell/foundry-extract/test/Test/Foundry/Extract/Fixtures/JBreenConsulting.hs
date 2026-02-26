{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           // test // fixtures // jbreenconsulting
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Extract.Fixtures.JBreenConsulting
Description : Test fixture for jbreenconsulting.com brand extraction
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Real-world test data extracted from jbreenconsulting.com.

== Extracted Brand Data

Primary Color: #8e43f0 (purple)
Typography: Raleway (headings, 600), Roboto (body), Open Sans
Tagline: "The Art of Branding. The Science of Strategy."
Spacing: WordPress preset scale (0.44rem to 5.06rem)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Extract.Fixtures.JBreenConsulting
  ( -- * Fixture
    jbreenScrapeResult
  , jbreenDomain
  , jbreenURL

    -- * Expected Values
  , expectedPrimaryColor
  , expectedHeadingFont
  , expectedBodyFont
  , expectedTagline
  ) where

import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BC
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Extract.Types
  ( AssetData (..)
  , AssetType (..)
  , CSSProperty (..)
  , CSSRule (..)
  , CSSSelector (..)
  , CSSStylesheet (..)
  , CSSValue (..)
  , ComputedStyle (..)
  , ElementStyles (..)
  , FontData (..)
  , FontFace (..)
  , ScrapeResult (..)
  , TextBlock (..)
  , TextBlockType (..)
  , TextContent (..)
  )

--------------------------------------------------------------------------------
-- Domain Constants
--------------------------------------------------------------------------------

-- | Source domain
jbreenDomain :: Text
jbreenDomain = "jbreenconsulting.com"

-- | Source URL
jbreenURL :: Text
jbreenURL = "https://jbreenconsulting.com/"

--------------------------------------------------------------------------------
-- Expected Values
--------------------------------------------------------------------------------

-- | Primary brand color (hex)
expectedPrimaryColor :: Text
expectedPrimaryColor = "#8e43f0"

-- | Expected heading font family
expectedHeadingFont :: Text
expectedHeadingFont = "Raleway"

-- | Expected body font family
expectedBodyFont :: Text
expectedBodyFont = "Roboto"

-- | Site tagline
expectedTagline :: Text
expectedTagline = "The Art of Branding. The Science of Strategy."

--------------------------------------------------------------------------------
-- Scrape Result Fixture
--------------------------------------------------------------------------------

-- | Complete ScrapeResult for jbreenconsulting.com
jbreenScrapeResult :: ScrapeResult
jbreenScrapeResult = ScrapeResult
  { srDomain = jbreenDomain
  , srURL = jbreenURL
  , srStylesheets = jbreenStylesheets
  , srComputedStyles = jbreenComputedStyles
  , srTextContent = jbreenTextContent
  , srFontData = jbreenFontData
  , srAssets = jbreenAssets
  , srRawHTML = jbreenRawHTML
  }

--------------------------------------------------------------------------------
-- Stylesheets
--------------------------------------------------------------------------------

-- | CSS stylesheets with brand colors
jbreenStylesheets :: Vector CSSStylesheet
jbreenStylesheets = V.fromList
  [ CSSStylesheet
      { cssSource = "inline"
      , cssRules = V.fromList
          -- Primary color usage (from WordPress/Elementor theme)
          [ CSSRule
              { cssSelector = CSSSelector ".bg-primary"
              , cssProperties = V.fromList
                  [ CSSProperty "background" (CSSColor "#8e43f0")
                  ]
              }
          , CSSRule
              { cssSelector = CSSSelector ".text-primary"
              , cssProperties = V.fromList
                  [ CSSProperty "color" (CSSColor "#8e43f0")
                  ]
              }
          , CSSRule
              { cssSelector = CSSSelector "a:hover"
              , cssProperties = V.fromList
                  [ CSSProperty "color" (CSSColor "#8e43f0")
                  ]
              }
          , CSSRule
              { cssSelector = CSSSelector ".octf-btn"
              , cssProperties = V.fromList
                  [ CSSProperty "background" (CSSColor "#8e43f0")
                  ]
              }
          -- WordPress preset colors
          , CSSRule
              { cssSelector = CSSSelector ":root"
              , cssProperties = V.fromList
                  [ CSSProperty "--wp--preset--color--black" (CSSColor "#000000")
                  , CSSProperty "--wp--preset--color--white" (CSSColor "#ffffff")
                  , CSSProperty "--wp--preset--color--cyan-bluish-gray" (CSSColor "#abb8c3")
                  ]
              }
          -- Typography
          , CSSRule
              { cssSelector = CSSSelector "h1, h2, h3, h4, h5, h6"
              , cssProperties = V.fromList
                  [ CSSProperty "font-family" (CSSFont "Raleway")
                  , CSSProperty "font-weight" (CSSNumber 600)
                  ]
              }
          , CSSRule
              { cssSelector = CSSSelector "body"
              , cssProperties = V.fromList
                  [ CSSProperty "font-family" (CSSFont "\"Open Sans\", sans-serif")
                  , CSSProperty "font-size" (CSSLength 16 "px")
                  , CSSProperty "line-height" (CSSNumber 1.6)
                  ]
              }
          -- Spacing scale (WordPress presets)
          , CSSRule
              { cssSelector = CSSSelector ":root"
              , cssProperties = V.fromList
                  [ CSSProperty "--wp--preset--spacing--20" (CSSLength 0.44 "rem")
                  , CSSProperty "--wp--preset--spacing--30" (CSSLength 0.67 "rem")
                  , CSSProperty "--wp--preset--spacing--40" (CSSLength 1.0 "rem")
                  , CSSProperty "--wp--preset--spacing--50" (CSSLength 1.5 "rem")
                  , CSSProperty "--wp--preset--spacing--60" (CSSLength 2.25 "rem")
                  , CSSProperty "--wp--preset--spacing--70" (CSSLength 3.38 "rem")
                  , CSSProperty "--wp--preset--spacing--80" (CSSLength 5.06 "rem")
                  ]
              }
          ]
      }
  ]

--------------------------------------------------------------------------------
-- Computed Styles
--------------------------------------------------------------------------------

-- | Computed styles for key elements
jbreenComputedStyles :: Vector ElementStyles
jbreenComputedStyles = V.fromList
  [ ElementStyles
      { esSelector = "h1.site-title"
      , esTagName = "H1"
      , esStyles = ComputedStyle
          { csColor = Just "#252525"
          , csBackgroundColor = Just "transparent"
          , csFontFamily = Just "Raleway"
          , csFontSize = Just 36
          , csFontWeight = Just 600
          , csLineHeight = Just 1.2
          , csMarginTop = Just 0
          , csMarginRight = Just 0
          , csMarginBottom = Just 16
          , csMarginLeft = Just 0
          , csPaddingTop = Just 0
          , csPaddingRight = Just 0
          , csPaddingBottom = Just 0
          , csPaddingLeft = Just 0
          }
      }
  , ElementStyles
      { esSelector = ".octf-btn"
      , esTagName = "A"
      , esStyles = ComputedStyle
          { csColor = Just "#ffffff"
          , csBackgroundColor = Just "#8e43f0"
          , csFontFamily = Just "Raleway"
          , csFontSize = Just 14
          , csFontWeight = Just 600
          , csLineHeight = Just 1.5
          , csMarginTop = Just 0
          , csMarginRight = Just 0
          , csMarginBottom = Just 0
          , csMarginLeft = Just 0
          , csPaddingTop = Just 12
          , csPaddingRight = Just 24
          , csPaddingBottom = Just 12
          , csPaddingLeft = Just 24
          }
      }
  , ElementStyles
      { esSelector = "body"
      , esTagName = "BODY"
      , esStyles = ComputedStyle
          { csColor = Just "#666666"
          , csBackgroundColor = Just "#ffffff"
          , csFontFamily = Just "\"Open Sans\""
          , csFontSize = Just 16
          , csFontWeight = Just 400
          , csLineHeight = Just 1.6
          , csMarginTop = Just 0
          , csMarginRight = Just 0
          , csMarginBottom = Just 0
          , csMarginLeft = Just 0
          , csPaddingTop = Just 0
          , csPaddingRight = Just 0
          , csPaddingBottom = Just 0
          , csPaddingLeft = Just 0
          }
      }
  ]

--------------------------------------------------------------------------------
-- Text Content
--------------------------------------------------------------------------------

-- | Extracted text content
jbreenTextContent :: TextContent
jbreenTextContent = TextContent
  { tcTitle = Just "jbreenconsulting.com \8211 The Art of Branding. The Science of Strategy."
  , tcHeadings = V.fromList
      [ TextBlock
          { tbText = "JBreen Consulting"
          , tbType = TBHeading1
          , tbSelector = "h1.site-title"
          }
      , TextBlock
          { tbText = "The Art of Branding. The Science of Strategy."
          , tbType = TBHeading2
          , tbSelector = "h2.tagline"
          }
      ]
  , tcParagraphs = V.fromList
      [ TextBlock
          { tbText = "Transform your brand with strategic insight and creative excellence."
          , tbType = TBParagraph
          , tbSelector = ".hero-text p"
          }
      ]
  , tcButtons = V.fromList
      [ TextBlock
          { tbText = "Get Started"
          , tbType = TBButton
          , tbSelector = ".octf-btn"
          }
      , TextBlock
          { tbText = "Learn More"
          , tbType = TBButton
          , tbSelector = ".btn-details"
          }
      ]
  , tcNavigation = V.fromList
      [ TextBlock
          { tbText = "Home"
          , tbType = TBLink
          , tbSelector = "nav a"
          }
      , TextBlock
          { tbText = "Services"
          , tbType = TBLink
          , tbSelector = "nav a"
          }
      , TextBlock
          { tbText = "About"
          , tbType = TBLink
          , tbSelector = "nav a"
          }
      , TextBlock
          { tbText = "Contact"
          , tbType = TBLink
          , tbSelector = "nav a"
          }
      ]
  , tcFooter = V.fromList
      [ TextBlock
          { tbText = "\169 2026 JBreen Consulting"
          , tbType = TBParagraph
          , tbSelector = "footer p"
          }
      ]
  }

--------------------------------------------------------------------------------
-- Font Data
--------------------------------------------------------------------------------

-- | Font information
jbreenFontData :: FontData
jbreenFontData = FontData
  { fdFaces = V.fromList
      [ FontFace
          { ffFamily = "Raleway"
          , ffWeight = Just "400"
          , ffStyle = Just "normal"
          , ffSrc = "https://jbreenconsulting.com/wp-content/fonts/raleway/1Ptug8zYS_SKggPNyC0ITw.woff2"
          }
      , FontFace
          { ffFamily = "Raleway"
          , ffWeight = Just "600"
          , ffStyle = Just "normal"
          , ffSrc = "https://jbreenconsulting.com/wp-content/fonts/raleway/1Ptug8zYS_SKggPNyC0ITw.woff2"
          }
      , FontFace
          { ffFamily = "Roboto"
          , ffWeight = Just "400"
          , ffStyle = Just "normal"
          , ffSrc = "https://jbreenconsulting.com/wp-content/fonts/roboto/KFOMCnqEu92Fr1ME7kSn66aGLdTylUAMQXC89YmC2DPNWubEbVmUiAo.woff2"
          }
      , FontFace
          { ffFamily = "Open Sans"
          , ffWeight = Just "400"
          , ffStyle = Just "normal"
          , ffSrc = "https://fonts.googleapis.com/css?family=Open+Sans"
          }
      ]
  , fdUsedFonts = Map.fromList
      [ ("Raleway", 45)
      , ("Roboto", 12)
      , ("Open Sans", 8)
      ]
  }

--------------------------------------------------------------------------------
-- Assets
--------------------------------------------------------------------------------

-- | Discovered assets
jbreenAssets :: Vector AssetData
jbreenAssets = V.fromList
  [ AssetData
      { adURL = "https://jbreenconsulting.com/wp-content/uploads/2023/06/cropped-JBreenDesigns_FaviconPurple-32x32.jpg"
      , adType = ATFavicon
      , adAlt = Nothing
      , adContext = "head"
      }
  , AssetData
      { adURL = "https://jbreenconsulting.com/wp-content/uploads/2023/06/cropped-JBreenDesigns_FaviconPurple-180x180.jpg"
      , adType = ATFavicon
      , adAlt = Nothing
      , adContext = "head"
      }
  ]

--------------------------------------------------------------------------------
-- Raw HTML (truncated for fixture)
--------------------------------------------------------------------------------

-- | Raw HTML content (SHA256 hash basis)
jbreenRawHTML :: ByteString
jbreenRawHTML = BC.pack $ unlines
  [ "<!doctype html>"
  , "<html lang=\"en-GB\">"
  , "<head>"
  , "<title>jbreenconsulting.com \8211 The Art of Branding. The Science of Strategy.</title>"
  , "<style>"
  , ".bg-primary { background: #8e43f0; }"
  , ".text-primary { color: #8e43f0; }"
  , "h1, h2, h3, h4, h5, h6 { font-family: Raleway; font-weight: 600; }"
  , "body { font-family: \"Open Sans\", sans-serif; }"
  , "</style>"
  , "</head>"
  , "<body>"
  , "<h1>JBreen Consulting</h1>"
  , "<h2>The Art of Branding. The Science of Strategy.</h2>"
  , "</body>"
  , "</html>"
  ]
