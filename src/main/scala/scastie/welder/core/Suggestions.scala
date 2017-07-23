package scastie.welder.core

trait Suggestions { self: Assistant =>
  type NamedSuggestion = (String, String)
}