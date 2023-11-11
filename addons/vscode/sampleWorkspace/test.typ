
#import "debug.typ": breakpoint

#let add(x, y) = none

// test

#let test = {
  1; add(1, 1)
}

#breakpoint(kind: "line")
