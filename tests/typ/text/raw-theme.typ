// Test code highlighting with custom theme.

---
#set page(width: 180pt)
#set text(6pt)
#set raw(theme: "/files/halcyon.tmTheme")
#show raw: it => {
  rect(
    width: 100%,
    inset: (x: 4pt, y: 5pt),
    radius: 4pt,
    fill: it.background,
    place(right, text(luma(240), it.lang)) + it,
  )
}

```typ
= Chapter 1
#lorem(100)

#let hi = "Hello World"
#show heading: emph
```

---
// Override background color

#set page(width: 180pt)
#set text(6pt)
#set raw(theme: "/files/halcyon.tmTheme")

#let background-color = {
  let data = xml("/files/halcyon.tmTheme").first()

  let find-child(elem, tag) = {
    elem.children.find(e => "tag" in e and e.tag == tag)
  }

  let find-kv(elem, key, tag) = {
    let idx = elem.children.position(e => "tag" in e and e.tag == "key" and e.children.first() == key)
    elem.children.slice(idx).find(e => "tag" in e and e.tag == tag)
  }

  let plist-dict = find-child(data, "dict")
  let plist-array = find-child(plist-dict, "array")
  let theme-setting = find-child(plist-array, "dict")
  let theme-setting-items = find-kv(theme-setting, "settings", "dict")
  let background-setting = find-kv(theme-setting-items, "background", "string")
  rgb(background-setting.children.first())
}

#set raw(background: background-color.darken(50%))
#show raw: it => {
  rect(
    width: 100%,
    inset: (x: 4pt, y: 5pt),
    radius: 4pt,
    fill: it.background,
    place(right, text(luma(240), it.lang)) + [#it],
  )
}

```typ
= Chapter 1
#lorem(100)

#let hi = "Hello World"
#show heading: emph
```

---

#set raw(theme: "/files/halcyon.tmTheme")
#set raw(foreground: red)
```txt
Foreground
```

---

#set raw(foreground: red)
```
Foreground
```

