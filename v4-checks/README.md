# Version 4 — the record of the checks of Theorems I and J

The full record is the zip [`coloured-sand-theorem-v4-checks.zip`](coloured-sand-theorem-v4-checks.zip) (the same file as on Zenodo, MD5 `2ec1421715a72b658b0c9f92eb788779`). The six reports are also here unzipped:

- [`odd_dance_constructor/`](odd_dance_constructor/): the report that found and proved Theorems I and J (Theorem $`\mathrm{D}_p`$, the lattices $L(\lambda)$, the twist and split moves, the Smith form of $M_p$), and the auditor's grading. Its scripts, logs and sealed prediction files (`work/SEALED_1.txt`, MD5 `0a9c3442e54c54c8cc880d9b2bc070b0`; `work/SEALED_2.txt`, MD5 `2f931de9eb3933c51a4ff3efb03274ab`) are in the zip.
- [`odd_dance_independent_reading/`](odd_dance_independent_reading/): the cold reading of that report by a separate reader with no access to the audit (verdict «holds with corrections»), and the auditor's grading. Its engines, logs, sealed predictions and the floor of the Smith form for odd $p$ written out line by line (`checks/THEOREM_F_ODD_P.md`) are in the zip.
- [`v3_cold_reading/`](v3_cold_reading/): the cold reading of version 3, whose corrections are listed in §13 of the paper, and the auditor's grading.

All the readers are instances of the AI system Claude (Anthropic). Third-party papers downloaded during the readings are not included. The code and logs of versions 1–3 are in [`../engines/`](../engines/) and [`../logs/`](../logs/).
