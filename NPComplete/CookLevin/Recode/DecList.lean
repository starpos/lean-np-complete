module

public import NPComplete.CookLevin.Recode.DecList.Foundation
public import NPComplete.CookLevin.Recode.DecList.BlockEncoding
public import NPComplete.CookLevin.Recode.DecList.RawPreprocess
public import NPComplete.CookLevin.Recode.DecList.Run
public import NPComplete.CookLevin.Recode.DecList.Output
public import NPComplete.CookLevin.Recode.DecList.Blocks
public import NPComplete.CookLevin.Recode.DecList.Iteration
public import NPComplete.CookLevin.Recode.DecList.RawComputable
public import NPComplete.CookLevin.Recode.DecList.Computable

/-!
  A list decoder for the fixed-width packed tape.

  The decoder consumes complete blocks from right to left.  A decoded bit is
  written on the blank side, leaving one blank separator between the output
  and the still unconsumed input.  Thus the final output is already in the
  canonical head-first orientation.
-/
