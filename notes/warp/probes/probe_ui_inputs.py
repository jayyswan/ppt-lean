"""Probe 10: which numbers can the UI actually set? (UI Automation on the ribbon and Font
dialog: list entries, spinner arrows, grow/shrink buttons, preset menu items. COM only selects
the text and reads the result back.) Takes over the screen while it runs.
Usage: py probe_ui_inputs.py [STEP...]   steps: list grow spacing dialog size"""
import time, ctypes, sys, json
try: ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception: pass
from pywinauto import Desktop
from warplab import *

steps = sys.argv[1:] or ["list", "grow", "spacing", "dialog", "size"]
res = {}
lab = Lab(visible=True)


def uiwin():
    t = lab.p.Name.split(".")[0]
    h = [x for x in Desktop(backend="uia").windows() if t in x.window_text()][0].handle
    return Desktop(backend="uia").window(handle=h)


def ctl(w, aid=None, name=None, ctype=None):
    kw = {}
    if aid: kw["auto_id"] = aid
    if name: kw["title"] = name
    if ctype: kw["control_type"] = ctype
    return w.child_window(**kw).wrapper_object()


try:
    win = lab.p.Windows(1); win.Activate(); win.WindowState = 3
    tb = lab.textbox("◗", box=(150, 100, 288, 288))
    tr = tb.TextFrame2.TextRange
    sel = lambda: (tr.Select(), time.sleep(0.4))
    sel(); w = uiwin()
    w.set_focus()

    if "list" in steps:
        cb = ctl(w, aid="FontSize", ctype="ComboBox")
        cb.expand(); time.sleep(0.8)
        items = [i.window_text() for i in cb.descendants(control_type="ListItem")]
        cb.collapse(); time.sleep(0.3)
        res["dropdown"] = items; print("dropdown:", items)

    if "grow" in steps:
        out = {}
        for start, aid, n in ((4000, "FontSizeDecrease", 80), (115, "FontSizeDecrease", 3),
                              (1, "FontSizeIncrease", 9), (3684, "FontSizeIncrease", 2)):
            tr.Font.Size = start; sel(); b = ctl(w, aid=aid)
            seq = [tr.Font.Size]
            for _ in range(n):
                b.invoke(); time.sleep(0.15); s = tr.Font.Size
                if s == seq[-1]: seq.append(s); break
                seq.append(s)
            out[f"{aid} from {start}"] = seq; print(aid, start, seq)
        res["grow"] = out
        tr.Font.Size = 72

    if "closure" in steps:
        up, dn = ctl(w, aid="FontSizeIncrease"), ctl(w, aid="FontSizeDecrease")
        seen = set(float(x) for x in res.get("dropdown", [])) or set(
            [8, 9, 10, 10.5, 11, 12, 14, 16, 18, 20, 24, 28, 32, 36, 40, 44, 48, 54, 60, 66, 72, 80, 88, 96])
        todo = sorted(seen); edges = {}
        while todo:
            s0 = todo.pop()
            for nm, b in (("up", up), ("dn", dn)):
                tr.Font.Size = s0; time.sleep(0.05); b.invoke(); time.sleep(0.12); s1 = tr.Font.Size
                edges[f"{s0} {nm}"] = s1
                if s1 not in seen: seen.add(s1); todo.append(s1)
        res["closure"] = sorted(seen); res["edges"] = edges
        print("reachable sizes", len(seen), sorted(seen))

    if "dialog" in steps:
        import threading
        from pywinauto import keyboard
        sel()
        threading.Thread(target=lambda: ctl(w, aid="FontDialogPowerPoint").invoke(), daemon=True).start()
        time.sleep(2.0)
        dlg = [d for d in Desktop(backend="uia").windows() if d.window_text() in ("Font", "Character Spacing")]
        if not dlg:
            dlg = [d for d in w.wrapper_object().descendants(control_type="Window")]
        d = dlg[0]; print("dialog:", d.window_text())
        def spin(name):
            sp = [c for c in d.descendants(control_type="Spinner") if c.window_text() == name][0]
            more = [c for c in sp.descendants(control_type="Button") if c.window_text() == "More"][0]
            less = [c for c in sp.descendants(control_type="Button") if c.window_text() == "Less"][0]
            ed = [c for c in sp.descendants(control_type="Edit")][0]
            return more, less, ed
        def walk(name, n=4):
            more, less, ed = spin(name); seq = [ed.window_text()]
            for _ in range(n): more.invoke(); time.sleep(0.15); seq.append(ed.window_text())
            for _ in range(2 * n): less.invoke(); time.sleep(0.15); seq.append(ed.window_text())
            for _ in range(n): more.invoke(); time.sleep(0.15)
            return seq
        out = {}
        out["Size spinner from 72"] = walk("Size")
        out["Offset spinner from 0%"] = walk("Offset")
        cbs = {c.window_text(): c for c in d.descendants(control_type="CheckBox")}
        for nm in ("Superscript", "Subscript"):
            cbs[nm].toggle(); time.sleep(0.3); out[nm + " offset"] = spin("Offset")[2].window_text()
            out[nm + " then More"] = walk("Offset", 2)
            cbs[nm].toggle(); time.sleep(0.3)
        [c for c in d.descendants(control_type="TabItem") if c.window_text() == "Character Spacing"][0].select()
        time.sleep(0.6)
        for c in d.descendants():
            try:
                if c.element_info.control_type in ("Spinner", "ComboBox", "CheckBox", "Edit", "Text"):
                    print("  CS:", repr(c.window_text()), c.element_info.control_type)
            except Exception: pass
        sps = [c.window_text() for c in d.descendants(control_type="Spinner")]
        print("  spinners:", sps)
        for nm in sps:
            try: out[f"CS spinner {nm}"] = walk(nm)
            except Exception as e: out[f"CS spinner {nm}"] = repr(e)
        res["dialog"] = out
        for k, v in out.items(): print(k, v)
        keyboard.send_keys("{ESC}"); time.sleep(0.5)

    if "size" in steps:
        tb.Select(); time.sleep(0.8)
        wr = w.wrapper_object()
        tabs = [c for c in wr.descendants(control_type="TabItem") if "Shape Format" in c.window_text()]
        print("tabs:", [t.window_text() for t in tabs])
        if tabs: tabs[0].select(); time.sleep(1.0)
        sp = [c for c in wr.descendants(control_type="Spinner")]
        print("spinners:", [c.window_text() for c in sp])
        out = {}
        from pywinauto import keyboard
        for i, c in enumerate(sp):
            nm = f"spinner #{i} {c.element_info.automation_id}"
            kids = [(x.window_text(), x.element_info.control_type) for x in c.descendants()]
            print(nm, "children", kids, "rect", c.rectangle())
            seq = [(c.window_text(), round(tb.Height, 3), round(tb.Width, 3))]
            c.set_focus(); time.sleep(0.3)
            for _ in range(3):
                keyboard.send_keys("{UP}"); time.sleep(0.4)
                seq.append((c.window_text(), round(tb.Height, 3), round(tb.Width, 3)))
            keyboard.send_keys("{ESC}"); time.sleep(0.3)
            out[nm] = seq; print(nm, seq)
        res["size_spinners"] = out

    if "spacingrange" in steps:
        import threading
        from pywinauto import keyboard
        out = {}
        for mode, val in [("Expanded", v) for v in ("1583", "1500", "1400", "1300", "1200", "1100", "1050", "1001", "1000.1")] + [("Condensed", v) for v in ("1583", "1500", "1200", "1001")]:
            tr.Font.Spacing = 0; sel()
            threading.Thread(target=lambda: ctl(w, aid="FontDialogPowerPoint").invoke(), daemon=True).start()
            time.sleep(1.5)
            d = ([x for x in Desktop(backend="uia").windows() if x.window_text() == "Font"] or
                 [x for x in w.wrapper_object().descendants(control_type="Window") if x.window_text() == "Font"])[0]
            [c for c in d.descendants(control_type="TabItem") if c.window_text() == "Character Spacing"][0].select()
            time.sleep(0.5)
            cb = [c for c in d.descendants(control_type="ComboBox") if c.window_text() == "Spacing"][0]
            cb.expand(); time.sleep(0.3)
            [c for c in cb.descendants(control_type="ListItem") if c.window_text() == mode][0].select(); time.sleep(0.3)
            try: cb.collapse()
            except Exception: pass
            sp = [c for c in d.descendants(control_type="Spinner") if c.window_text() == "By"][0]
            ed = sp.descendants(control_type="Edit")[0]
            ed.set_focus(); time.sleep(0.2); keyboard.send_keys("^a", pause=0.2); keyboard.send_keys("{DEL}", pause=0.2)
            keyboard.send_keys(val, pause=0.15); time.sleep(0.3); typed = ed.window_text()
            keyboard.send_keys("{TAB}", pause=0.2); time.sleep(0.5)
            shown = ed.window_text()
            ok = [c for c in d.descendants(control_type="Button") if c.window_text() == "OK"][0]
            threading.Thread(target=ok.invoke, daemon=True).start(); time.sleep(1.2)
            msg = [x for x in list(Desktop(backend="uia").windows()) + list(w.wrapper_object().descendants(control_type="Window"))
                   if x.window_text() in ("Microsoft PowerPoint", "Font")]
            texts = []
            for m in msg:
                texts += [c.window_text() for c in m.descendants(control_type="Text") if c.window_text()]
            if msg:
                keyboard.send_keys("{ENTER}"); time.sleep(0.6)
                for x in list(Desktop(backend="uia").windows()) + list(w.wrapper_object().descendants(control_type="Window")):
                    if x.window_text() == "Font": keyboard.send_keys("{ESC}"); time.sleep(0.5); break
            out[f"{mode} {val}"] = dict(typed=typed, field_after_tab=shown, spacing=tr.Font.Spacing, dialog_text=texts[:6])
            print(mode, val, out[f"{mode} {val}"])
        res["spacing_range"] = out

    if "spacing" in steps:
        sel()
        mi = ctl(w, aid="CharacterSpacingGallery")
        mi.expand(); time.sleep(1.0)
        for d in Desktop(backend="uia").windows():
            for c in d.descendants():
                try: t = c.window_text()
                except Exception: continue
                if any(k in t for k in ("Tight", "Loose", "Normal", "More Spacing")):
                    print("  found", repr(t), c.element_info.control_type, repr(d.window_text()), d.element_info.class_name)
        names = [i.window_text() for i in Desktop(backend="uia").window(class_name_re=".*").descendants(control_type="MenuItem")] if False else None
        menu_items = [c for c in w.wrapper_object().descendants(control_type="MenuItem")] + \
                     [c for d in Desktop(backend="uia").windows() for c in d.descendants(control_type="MenuItem")
                      if d.window_text() == ""]
        labels = []
        for c in menu_items:
            t = c.window_text()
            if t and t not in labels: labels.append(t)
        print("spacing menu:", labels)
        try: mi.collapse()
        except Exception: pass
        out = {}
        for lab_name in ("Very Tight", "Tight", "Normal", "Loose", "Very Loose"):
            sel(); mi = ctl(w, aid="CharacterSpacingGallery"); mi.expand(); time.sleep(0.6)
            hit = None
            for c in w.wrapper_object().descendants(control_type="ListItem"):
                if c.window_text() == lab_name: hit = c; break
            if hit is None: out[lab_name] = None; continue
            name = hit.window_text()
            try: hit.invoke()
            except Exception: hit.select()
            time.sleep(0.4); out[name] = tr.Font.Spacing
        res["spacing_presets"] = out; print("spacing presets:", out)
finally:
    json.dump(res, open("ui_inputs.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    time.sleep(0.5); lab.close()
