module

public import NPComplete.BoundedWhile.Basic

/-!
# Public-import intermediary

An intermediary with no declarations isolates what `public import` contributes
on its own. Re-exporting `Basic` here lets the companion importers test whether the
bodies of its definitions stay unfoldable across the additional module boundary.
-/
