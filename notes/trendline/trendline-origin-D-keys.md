# trendline-origin-D: keyboard/mouse routes to change Forecast > Backward

Status: INCOMPLETE, aborted at coordinator request. No key/wheel actions on the Backward box were tested.

What was done: set up a presentation via COM (scatter chart, y=2x^1.5, power trendline, x min 0);
tried to open the Format Trendline pane by UI (Ctrl+1 / clicking the curve). Never reached the pane,
so no control type/pattern data for the Backward box was obtained.

| Action | Result |
|---|---|
| Up/Down/Ctrl+Up/Shift+Up/PgUp/PgDn/wheel/Alt+Down/F4 on Backward | NOT TESTED |

Obstacles found (useful for anyone repeating this):
- `sys.coinit_flags=2` must be set before importing pywinauto, otherwise win32com proxies die
  ("Object is not connected to server") once pywinauto is imported.
- `Presentations.Add(True)` returns a broken dynamic object; use `Add(-1)`.
- Window focus contention with other agents' PowerPoint windows; verify foreground before keystrokes.
- PowerPoint crashed/restarted during the session (RPC server unavailable); chart-workbook COM is flaky.
- `trendline.Select()` via COM did not visibly select it after maximizing; the pane did not open.

Verdict: undetermined by this probe; superseded by another agent's route (blank-y row at x = 0).
