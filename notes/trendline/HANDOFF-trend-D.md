start: scratch dir created
step1: Add(True) broke pres object; use Add(-1). Leftover Presentation7 (mine, chart) from failed run; closing by scan denied, will report
step2: COM proxy died after pywinauto import (apartment); fix coinit_flags=2. Leaked mine: Presentation14,16 (+7); can't close without object (will report)
step3: Excel RPC failures in build (Presentation20/21 leaked); retrying
step4: focus contention with other agent's windows; added fg() helper that verifies foreground before keystrokes
step5: PowerPoint crashed/restarted (AutoRecovered docs appeared; none closed by me). All earlier leaked presentations gone. retrying
step6: wrapped up at coordinator request; notes written; pres.Close in finally ran for Presentation2 (last run); earlier leaked ones were lost in PowerPoint crash/restart
