//! Font handling.

mod book;
mod variant;

pub use self::book::{Coverage, FontBook, FontFlags, FontInfo};
pub use self::variant::{FontStretch, FontStyle, FontVariant, FontWeight};

use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use ttf_parser::GlyphId;

use self::book::find_name;
use crate::eval::Cast;
use crate::geom::Em;
use crate::util::Bytes;

/// An OpenType font.
///
/// Values of this type are cheap to clone and hash.
#[derive(Clone)]
pub struct Font(Arc<Repr>);

/// The internal representation of a font.
struct Repr {
    /// The raw font data, possibly shared with other fonts from the same
    /// collection. The vector's allocation must not move, because `ttf` points
    /// into it using unsafe code.
    data: Bytes,
    /// The font's index in the buffer.
    index: u32,
    /// Metadata about the font.
    info: FontInfo,
    /// The font's metrics.
    metrics: FontMetrics,
    /// The underlying ttf-parser face.
    ttf: ttf_parser::Face<'static>,
    /// The underlying rustybuzz face.
    rusty: rustybuzz::Face<'static>,
}

impl Font {
    /// Parse a font from data and collection index.
    pub fn new(data: Bytes, index: u32) -> Option<Self> {
        // Safety:
        // - The slices's location is stable in memory:
        //   - We don't move the underlying vector
        //   - Nobody else can move it since we have a strong ref to the `Arc`.
        // - The internal 'static lifetime is not leaked because its rewritten
        //   to the self-lifetime in `ttf()`.
        let slice: &'static [u8] =
            unsafe { std::slice::from_raw_parts(data.as_ptr(), data.len()) };

        let ttf = ttf_parser::Face::parse(slice, index).ok()?;
        let rusty = rustybuzz::Face::from_slice(slice, index)?;
        let metrics = FontMetrics::from_ttf(&ttf);
        let info = FontInfo::from_ttf(&ttf)?;

        Some(Self(Arc::new(Repr { data, index, info, metrics, ttf, rusty })))
    }

    pub fn new_dummy(info: FontInfo, metrics: FontMetrics) -> Option<Self> {
        const DUMMY_STR: &str = "00010000000a0080000300204f532f3256927379000000ac00000060636d6170000d01910000010c0000013a676c7966fd279a9d00000248000000286865616421179c5f00000270000000366868656104de00e8000002a800000024686d747801760022000002cc000000046c6f636100000014000002d0000000046d61787000040008000002d4000000206e616d656ed98057000002f400000174706f737400350001000004680000002400040176019000050000029902cc0000008f029902cc000001eb00330109000002000603000000000000000000011000000000000000000000005066456400c0ffffffff032cff2c005c032c00d400000001000000000318000000000020000100000003000000030000001c0001000000000034000300010000001c0004001800000002000200000000ffff0000ffff00010000000001060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200220000013202aa0003000700003711211127331123220110eecccc0002aafd5622026600000001000000010000d10e35635f0f3cf5000b040000000000e052ac5c00000000e052ac5c00220000013202aa00000008000200000000000000010000032cff2c005c0176002200440132000100000000000000000000000000000001017600220000001400010000000100080002000000000000000000000000000000000000000000000000000c009600010000000000010005000000010000000000020006000500010000000000030011000b00010000000000040005001c0001000000000005001e00210001000000000006000b003f0003000104090001000a004a0003000104090002000c00540003000104090003002200600003000104090004000a00820003000104090005003c008c0003000104090006001600c864756d6d794d656469756d64756d6d7920312e30203a2064756d6d7964756d6d7956657273696f6e20312e303b20466f6e74456469746f72202876312e302974797073742d64756d6d7900640075006d006d0079004d0065006400690075006d00640075006d006d007900200031002e00300020003a002000640075006d006d007900640075006d006d007900560065007200730069006f006e00200031002e0030003b00200046006f006e00740045006400690074006f00720020002800760031002e0030002900740079007000730074002d00640075006d006d0079000200000000000000320000000000000000000000000000000000000000000100010000";
        let dummy_data: Vec<u8> = (0..DUMMY_STR.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&DUMMY_STR[i..i + 2], 16).unwrap())
            .collect();
        let ttf_len = dummy_data.len();

        // append entropy to the dummy data to avoid comemo issues
        let mut dummy_data = dummy_data;
        dummy_data.extend_from_slice(unsafe {
            std::slice::from_raw_parts(
                &info as *const FontInfo as *const u8,
                std::mem::size_of::<FontInfo>(),
            )
        });
        dummy_data.extend_from_slice(unsafe {
            std::slice::from_raw_parts(
                &metrics as *const FontMetrics as *const u8,
                std::mem::size_of::<FontMetrics>(),
            )
        });

        let data = Bytes::from(dummy_data);
        let slice: &'static [u8] =
            unsafe { std::slice::from_raw_parts(data.as_ptr(), ttf_len) };

        let ttf = ttf_parser::Face::parse(slice, 0).ok()?;
        let rusty = rustybuzz::Face::from_slice(slice, 0)?;

        Some(Self(Arc::new(Repr { data, index: 0, info, metrics, ttf, rusty })))
    }

    pub fn is_dummy(&self) -> bool {
        let name = self.0.ttf.names().get(ttf_parser::name_id::POST_SCRIPT_NAME);
        // utf-16 be, dummy
        matches!(
            name.map(|n| n.name),
            Some(&[0, 0x64, 0, 0x75, 0, 0x6d, 0, 0x6d, 0, 0x79])
        )
    }

    /// Parse all fonts in the given data.
    pub fn iter(data: Bytes) -> impl Iterator<Item = Self> {
        let count = ttf_parser::fonts_in_collection(&data).unwrap_or(1);
        (0..count).filter_map(move |index| Self::new(data.clone(), index))
    }

    /// The underlying buffer.
    pub fn data(&self) -> &Bytes {
        &self.0.data
    }

    /// The font's index in the buffer.
    pub fn index(&self) -> u32 {
        self.0.index
    }

    /// The font's metadata.
    pub fn info(&self) -> &FontInfo {
        &self.0.info
    }

    /// The font's metrics.
    pub fn metrics(&self) -> &FontMetrics {
        &self.0.metrics
    }

    /// The number of font units per one em.
    pub fn units_per_em(&self) -> f64 {
        self.0.metrics.units_per_em
    }

    /// Convert from font units to an em length.
    pub fn to_em(&self, units: impl Into<f64>) -> Em {
        Em::from_units(units, self.units_per_em())
    }

    /// Look up the horizontal advance width of a glyph.
    pub fn advance(&self, glyph: u16) -> Option<Em> {
        self.0
            .ttf
            .glyph_hor_advance(GlyphId(glyph))
            .map(|units| self.to_em(units))
    }

    /// Lookup a name by id.
    pub fn find_name(&self, id: u16) -> Option<String> {
        find_name(&self.0.ttf, id)
    }

    /// A reference to the underlying `ttf-parser` face.
    pub fn ttf(&self) -> &ttf_parser::Face<'_> {
        // We can't implement Deref because that would leak the
        // internal 'static lifetime.
        &self.0.ttf
    }

    /// A reference to the underlying `rustybuzz` face.
    pub fn rusty(&self) -> &rustybuzz::Face<'_> {
        // We can't implement Deref because that would leak the
        // internal 'static lifetime.
        &self.0.rusty
    }
}

impl Hash for Font {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.data.hash(state);
        self.0.index.hash(state);
    }
}

impl Debug for Font {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Font({})", self.info().family)
    }
}

impl Eq for Font {}

impl PartialEq for Font {
    fn eq(&self, other: &Self) -> bool {
        self.0.data == other.0.data && self.0.index == other.0.index
    }
}

/// Metrics of a font.
#[derive(Debug, Copy, Clone)]
pub struct FontMetrics {
    /// How many font units represent one em unit.
    pub units_per_em: f64,
    /// The distance from the baseline to the typographic ascender.
    pub ascender: Em,
    /// The approximate height of uppercase letters.
    pub cap_height: Em,
    /// The approximate height of non-ascending lowercase letters.
    pub x_height: Em,
    /// The distance from the baseline to the typographic descender.
    pub descender: Em,
    /// Recommended metrics for a strikethrough line.
    pub strikethrough: LineMetrics,
    /// Recommended metrics for an underline.
    pub underline: LineMetrics,
    /// Recommended metrics for an overline.
    pub overline: LineMetrics,
}

impl FontMetrics {
    /// Extract the font's metrics.
    pub fn from_ttf(ttf: &ttf_parser::Face) -> Self {
        let units_per_em = f64::from(ttf.units_per_em());
        let to_em = |units| Em::from_units(units, units_per_em);

        let ascender = to_em(ttf.typographic_ascender().unwrap_or(ttf.ascender()));
        let cap_height = ttf.capital_height().filter(|&h| h > 0).map_or(ascender, to_em);
        let x_height = ttf.x_height().filter(|&h| h > 0).map_or(ascender, to_em);
        let descender = to_em(ttf.typographic_descender().unwrap_or(ttf.descender()));
        let strikeout = ttf.strikeout_metrics();
        let underline = ttf.underline_metrics();

        let strikethrough = LineMetrics {
            position: strikeout.map_or(Em::new(0.25), |s| to_em(s.position)),
            thickness: strikeout
                .or(underline)
                .map_or(Em::new(0.06), |s| to_em(s.thickness)),
        };

        let underline = LineMetrics {
            position: underline.map_or(Em::new(-0.2), |s| to_em(s.position)),
            thickness: underline
                .or(strikeout)
                .map_or(Em::new(0.06), |s| to_em(s.thickness)),
        };

        let overline = LineMetrics {
            position: cap_height + Em::new(0.1),
            thickness: underline.thickness,
        };

        Self {
            units_per_em,
            ascender,
            cap_height,
            x_height,
            descender,
            strikethrough,
            underline,
            overline,
        }
    }

    /// Look up a vertical metric.
    pub fn vertical(&self, metric: VerticalFontMetric) -> Em {
        match metric {
            VerticalFontMetric::Ascender => self.ascender,
            VerticalFontMetric::CapHeight => self.cap_height,
            VerticalFontMetric::XHeight => self.x_height,
            VerticalFontMetric::Baseline => Em::zero(),
            VerticalFontMetric::Descender => self.descender,
        }
    }
}

/// Metrics for a decorative line.
#[derive(Debug, Copy, Clone)]
pub struct LineMetrics {
    /// The vertical offset of the line from the baseline. Positive goes
    /// upwards, negative downwards.
    pub position: Em,
    /// The thickness of the line.
    pub thickness: Em,
}

/// Identifies a vertical metric of a font.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Cast)]
pub enum VerticalFontMetric {
    /// The font's ascender, which typically exceeds the height of all glyphs.
    Ascender,
    /// The approximate height of uppercase letters.
    CapHeight,
    /// The approximate height of non-ascending lowercase letters.
    XHeight,
    /// The baseline on which the letters rest.
    Baseline,
    /// The font's ascender, which typically exceeds the depth of all glyphs.
    Descender,
}
