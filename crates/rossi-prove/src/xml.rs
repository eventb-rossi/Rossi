//! Shared attribute access for the streaming XML readers.

use quick_xml::events::BytesStart;

/// Every attribute of an element start tag, keys and values decoded
/// leniently: invalid UTF-8 is replaced and an unescapable value is
/// kept raw rather than failing the read.
pub(crate) fn attrs(e: &BytesStart<'_>) -> Vec<(String, String)> {
    e.attributes()
        .flatten()
        .map(|attr| {
            let key = String::from_utf8_lossy(attr.key.as_ref()).into_owned();
            let raw = String::from_utf8_lossy(&attr.value);
            let value = match quick_xml::escape::unescape(&raw) {
                Ok(cow) => cow.into_owned(),
                Err(_) => raw.into_owned(),
            };
            (key, value)
        })
        .collect()
}

/// The value of `key` among [`attrs`]' pairs.
pub(crate) fn get<'a>(attrs: &'a [(String, String)], key: &str) -> Option<&'a str> {
    attrs
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.as_str())
}
