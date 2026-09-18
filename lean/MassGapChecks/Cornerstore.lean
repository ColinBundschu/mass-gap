import MassGap.Cornerstore

/-! # Checks: the corner disconjugacy certificate's store

The store's certificate read (`disconjC_read`) at the theorem route,
the assembled read's kernel verification the content module's own
at its stated data, and the certificate's derived rates read at the
store. -/

namespace cornerpivot.cornerstore

open ground cornerpivot

theorem pin1 : certRead preR disconjC := disconjC_read

end cornerpivot.cornerstore
