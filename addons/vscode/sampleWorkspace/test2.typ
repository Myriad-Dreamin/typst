#let add(x, y) = { x + y; none }

#let x() = add(1, 1)

#show: (content) => {
  content
}

#x()
