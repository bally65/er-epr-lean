"""ER=EPR 玩具零件庫：這一路在做什麼（ManimGX 解說動畫）。

故事稿與分鏡見同目錄的 STORY.md。所有圖都是示意：曲線形狀對，數值不按比例。
渲染：manimgx render journey.py Journey      （草稿：-r 1280x720 --fps 30）
檢查：manimgx inspect journey.py
"""

import math

import manimgx as m


def caption(text: str) -> m.Text:
    return m.Text(text, font_size=28, color=m.GRAY_A).move_to([0, -3.35, 0])


def tile(text: str, color) -> m.VGroup:
    label = m.Text(text, font_size=24)
    box = m.Rectangle(width=label.width + 0.45, height=label.height + 0.35, color=color)
    box.move_to(label.get_center())
    return m.VGroup(box, label)


def node(point, name: str, desc: str, color) -> m.VGroup:
    dot = m.Dot(point, radius=0.16, color=color)
    label = m.Text(name, font_size=30).next_to(dot, m.UP, buff=0.2)
    sub = m.Text(desc, font_size=22, color=m.GRAY_B).next_to(dot, m.DOWN, buff=0.25)
    return m.VGroup(dot, label, sub)


class Journey(m.Scene):
    def clear(self, *mobs) -> None:
        self.play(*[m.FadeOut(x) for x in mobs], run_time=0.8)

    def construct(self) -> None:
        # ── 1 問題 ─────────────────────────────────────────────
        title = m.Text("ER = EPR ？", font_size=60).to_edge(m.UP)
        bh1 = m.Circle(radius=0.6, color=m.WHITE, fill_opacity=0.15).move_to([-5.2, 0.3, 0])
        bh2 = m.Circle(radius=0.6, color=m.WHITE, fill_opacity=0.15).move_to([-2.4, 0.3, 0])
        tube = m.VGroup(
            m.Line([-4.65, 0.62, 0], [-2.95, 0.62, 0], color=m.BLUE),
            m.Line([-4.65, -0.02, 0], [-2.95, -0.02, 0], color=m.BLUE),
        )
        er_label = m.Text("ER：蟲洞（幾何）", font_size=30).move_to([-3.8, -1.2, 0])
        d1 = m.Dot([2.4, 0.3, 0], radius=0.16, color=m.YELLOW)
        d2 = m.Dot([5.2, 0.3, 0], radius=0.16, color=m.YELLOW)
        link = m.Line([2.4, 0.3, 0], [5.2, 0.3, 0], color=m.YELLOW, stroke_width=6)
        epr_label = m.Text("EPR：糾纏（量子）", font_size=30).move_to([3.8, -1.2, 0])
        eq = m.Text("＝？", font_size=64).move_to([0, 0.3, 0])
        cap1 = caption("ER=EPR 是一個猜想：蟲洞和糾纏是同一件事。它不是數學定理。")
        self.play(m.Write(title))
        self.play(m.FadeIn(bh1), m.FadeIn(bh2), m.Create(tube), m.FadeIn(er_label))
        self.play(m.FadeIn(d1), m.FadeIn(d2), m.Create(link), m.FadeIn(epr_label))
        self.play(m.Write(eq), m.FadeIn(cap1))
        self.wait(3)
        self.clear(bh1, bh2, tube, er_label, d1, d2, link, epr_label, eq, cap1)
        self.play(m.FadeOut(title), run_time=0.8)

        # ── 2 策略：把洞逼到角落 ─────────────────────────────────
        hole = m.Circle(radius=1.25, color=m.GRAY)
        hole_label = m.Text("ER=EPR\n本身", font_size=28, color=m.GRAY_B).move_to(hole.get_center())
        left_tiles = m.VGroup(
            tile("Kruskal 不可穿越", m.BLUE),
            tile("β = 8πM", m.BLUE),
            tile("Unruh 熱分佈", m.BLUE),
        ).arrange(m.DOWN, buff=0.35).move_to([-5.0, 0.2, 0])
        right_tiles = m.VGroup(
            tile("不可通訊", m.YELLOW),
            tile("次可加性", m.YELLOW),
            tile("Landauer", m.YELLOW),
            tile("一夫一妻", m.YELLOW),
            tile("糾纏交換", m.YELLOW),
        ).arrange(m.DOWN, buff=0.25).move_to([5.0, 0.2, 0])
        cap2 = caption("我們不去填那個洞：把兩側能寫成數學的零件證成定理，把洞逼到角落。")
        self.play(m.Create(hole), m.FadeIn(hole_label))
        self.play(m.LaggedStart(*[m.FadeIn(t) for t in left_tiles], lag_ratio=0.3),
                  m.LaggedStart(*[m.FadeIn(t) for t in right_tiles], lag_ratio=0.3),
                  m.FadeIn(cap2), run_time=2.5)
        self.play(left_tiles.animate.shift(1.5 * m.RIGHT), right_tiles.animate.shift(1.5 * m.LEFT),
                  hole.animate.scale(0.8), run_time=2)
        self.wait(3)
        self.clear(hole, hole_label, left_tiles, right_tiles, cap2)

        # ── 3 洞的形狀①：不可能定理 ─────────────────────────────
        head3 = m.Text("洞的形狀一：固定的有限維系統對不上黑洞", font_size=34).move_to([0, 2.9, 0])
        axes = m.Axes(x_range=[0, 4, 1], y_range=[0, 3, 1], x_length=7, y_length=4.2).move_to([-0.8, -0.2, 0])

        def falling(x: float) -> float:
            return 2.2 * math.exp(-0.6 * x) + 0.2

        def rising(x: float) -> float:
            return 0.18 * x * x

        lo, hi = 1.0, 3.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if falling(mid) > rising(mid):
                lo = mid
            else:
                hi = mid
        x_star = (lo + hi) / 2
        curve_fixed = axes.plot(falling, x_range=[0, 4], color=m.BLUE)
        curve_bh = axes.plot(rising, x_range=[0, 4], color=m.RED)
        label_fixed = m.Text("固定系統的熵：往下", font_size=24, color=m.BLUE).move_to([4.6, 0.6, 0])
        label_bh = m.Text("黑洞的熵 β²/16π：往上", font_size=24, color=m.RED).move_to([4.6, 1.6, 0])
        cross = m.Dot(axes.c2p(x_star, rising(x_star)), radius=0.12, color=m.WHITE)
        x_name = m.Text("β", font_size=28).next_to(axes.c2p(4, 0), m.RIGHT, buff=0.2)
        y_name = m.Text("S", font_size=28).next_to(axes.c2p(0, 3), m.UP, buff=0.15)
        cap3 = caption("（示意圖）兩條曲線只交在一點：單一溫度對得上，一整段溫度不可能。")
        self.play(m.Write(head3), m.Create(axes), m.FadeIn(x_name), m.FadeIn(y_name))
        self.play(m.Create(curve_fixed), m.FadeIn(label_fixed))
        self.play(m.Create(curve_bh), m.FadeIn(label_bh))
        self.play(m.GrowFromCenter(cross), m.FadeIn(cap3))
        self.wait(3)
        self.clear(axes, x_name, y_name, curve_fixed, curve_bh, label_fixed, label_bh, cross, cap3)

        q_fixed = m.VGroup(
            m.MathTex(r"\exists H\ \forall \beta", color=m.RED),
            m.Text("固定一個 H，對所有溫度：做不到", font_size=30),
        ).arrange(m.RIGHT, buff=0.5).move_to([0, 0.8, 0])
        q_vary = m.VGroup(
            m.MathTex(r"\forall \beta\ \exists H", color=m.GREEN),
            m.Text("每個溫度各換一個 H：做得到", font_size=30),
        ).arrange(m.RIGHT, buff=0.5).move_to([0, -0.6, 0])
        cap3b = caption("不可能定理排除的只有「H 固定」：洞剩下的出口是隨質量變的 Hilbert 空間。")
        self.play(m.FadeIn(q_fixed))
        self.play(m.FadeIn(q_vary), m.FadeIn(cap3b))
        self.wait(3.5)
        self.clear(head3, q_fixed, q_vary, cap3b)

        # ── 4 洞的形狀②：AMPS ─────────────────────────────────
        head4 = m.Text("洞的形狀二：糾纏不能共享（一夫一妻）", font_size=34).move_to([0, 2.9, 0])
        a = node([-4.5, 0, 0], "A", "黑洞內部", m.WHITE)
        b = node([0, 0, 0], "B", "晚期輻射", m.WHITE)
        r = node([4.5, 0, 0], "R", "早期輻射", m.WHITE)
        ab = m.Line([-4.3, 0, 0], [-0.2, 0, 0], color=m.YELLOW, stroke_width=7)
        ab_note = m.Text("視界平滑：A–B 最大糾纏", font_size=24, color=m.YELLOW).move_to([-2.25, 1.35, 0])
        br = m.Line([0.2, 0, 0], [4.3, 0, 0], color=m.RED, stroke_width=4)
        x_mark = m.VGroup(
            m.Line([1.95, -0.35, 0], [2.55, 0.35, 0], color=m.RED, stroke_width=8),
            m.Line([1.95, 0.35, 0], [2.55, -0.35, 0], color=m.RED, stroke_width=8),
        )
        br_note = m.Text("資訊不丟：B–R 最大相關？", font_size=24, color=m.RED).move_to([2.25, 1.35, 0])
        mono = m.MathTex(r"I(B{:}R) = 0", color=m.RED).move_to([2.25, -1.6, 0])
        cap4 = caption("A–B 一旦是純態，B 與 R 就毫無相關：兩個要求不能同時成立（AMPS 矛盾）。")
        self.play(m.Write(head4), m.FadeIn(a), m.FadeIn(b), m.FadeIn(r))
        self.play(m.Create(ab), m.FadeIn(ab_note))
        self.play(m.Create(br), m.FadeIn(br_note))
        self.play(m.Create(x_mark), m.Write(mono), m.FadeIn(cap4))
        self.wait(4)
        self.clear(head4, a, b, r, ab, ab_note, br, br_note, x_mark, mono, cap4)

        # ── 5 線是轉手，不是剪斷 ─────────────────────────────────
        head5 = m.Text("線是轉手，不是剪斷", font_size=34).move_to([0, 2.9, 0])
        sys_node = node([-3.0, 0.3, 0], "系統", "疊加態 |+⟩", m.WHITE)
        ptr_node = node([3.0, 0.3, 0], "儀器", "|0⟩", m.WHITE)
        coh = m.Text("干涉項 1/2", font_size=26, color=m.GREEN).move_to([-3.0, -1.4, 0])
        coh0 = m.Text("干涉項 0", font_size=26, color=m.RED).move_to([-3.0, -1.4, 0])
        sp = m.Line([-2.8, 0.3, 0], [2.8, 0.3, 0], color=m.YELLOW, stroke_width=6)
        cnot = m.Text("CNOT（測量）", font_size=24, color=m.YELLOW).move_to([0, 0.85, 0])
        cap5 = caption("觀測：系統和儀器接上線。只看系統，干涉項歸零、熵 0→ln 2；整體仍是純態。")
        self.play(m.Write(head5), m.FadeIn(sys_node), m.FadeIn(ptr_node), m.FadeIn(coh))
        self.play(m.Create(sp), m.FadeIn(cnot), m.Transform(coh, coh0), m.FadeIn(cap5), run_time=1.5)
        self.wait(3.5)
        self.clear(sys_node, ptr_node, coh, sp, cnot, cap5)

        qa = node([-4.5, 1.2, 0], "A", "", m.WHITE)
        qb = node([-1.3, -0.9, 0], "B", "", m.WHITE)
        qc = node([1.3, -0.9, 0], "C", "", m.WHITE)
        qd = node([4.5, 1.2, 0], "D", "", m.WHITE)
        l_ab = m.Line([-4.4, 1.05, 0], [-1.4, -0.75, 0], color=m.YELLOW, stroke_width=6)
        l_cd = m.Line([1.4, -0.75, 0], [4.4, 1.05, 0], color=m.YELLOW, stroke_width=6)
        meas = m.Rectangle(width=3.8, height=2.0, color=m.ORANGE).move_to([0, -0.65, 0])
        meas_label = m.Text("B、C 聯合測量", font_size=24, color=m.ORANGE).move_to([0, -2.0, 0])
        l_ad = m.Line([-4.3, 1.2, 0], [4.3, 1.2, 0], color=m.YELLOW, stroke_width=6)
        cap5b = caption("交換：A、D 從沒碰過面，中間一次糾纏的測量，就接成一條線（機率 1/4）。")
        cap5c = caption("但四種結果平均起來，A–D 什麼都沒變：接得上糾纏，傳不了訊息。")
        self.play(m.FadeIn(qa), m.FadeIn(qb), m.FadeIn(qc), m.FadeIn(qd), m.Create(l_ab), m.Create(l_cd))
        self.play(m.Create(meas), m.FadeIn(meas_label), m.FadeIn(cap5b))
        self.play(m.FadeOut(l_ab), m.FadeOut(l_cd), m.Create(l_ad), run_time=1.5)
        self.wait(2.5)
        self.play(m.Transform(cap5b, cap5c))
        self.wait(3)
        self.clear(head5, qa, qb, qc, qd, meas, meas_label, l_ad, cap5b)

        # ── 6 怎麼確定是真的 ─────────────────────────────────────
        head6 = m.Text("怎麼確定這些是真的", font_size=34).move_to([0, 2.9, 0])
        stats = m.VGroup(
            m.Text("599 條定理，只用標準公理", font_size=30),
            m.Text("95 份反向演習：故意改壞，確認會紅", font_size=30),
            m.Text("91 條耦合斷言：機械確認誰用到誰", font_size=30),
            m.Text("0 個 sorry", font_size=30),
        ).arrange(m.DOWN, buff=0.45).move_to([0, 0.3, 0])
        self.play(m.Write(head6))
        self.play(m.LaggedStart(*[m.FadeIn(s) for s in stats], lag_ratio=0.4), run_time=3)
        self.wait(2.5)
        self.clear(head6, stats)

        ending = m.Text("洞還在，但形狀更清楚了。", font_size=48).move_to([0, 0.4, 0])
        footer = m.Text("Lean 4 ＋ mathlib · ER=EPR 玩具零件庫 · 2026-10", font_size=24,
                        color=m.GRAY_B).move_to([0, -1.2, 0])
        self.play(m.Write(ending))
        self.play(m.FadeIn(footer))
        self.wait(3)
