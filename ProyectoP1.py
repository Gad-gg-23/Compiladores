import tkinter as tk
from tkinter import messagebox

# -----------------------------
# Modelo (NFA) con transiciones
# -----------------------------
class Transition:
    # kind: "epsilon" | "symbol" | "range"
    def __init__(self, kind: str, value, to_state: int):
        self.kind = kind
        self.value = value
        self.to_state = to_state

    def label(self) -> str:
        if self.kind == "epsilon":
            return "ε"
        if self.kind == "symbol":
            return str(self.value)
        if self.kind == "range":
            low, high = self.value
            return f"{low}-{high}"
        return "?"

class State:
    def __init__(self, sid: int, is_final: bool = False):
        self.sid = sid
        self.is_final = is_final
        self.transitions: list[Transition] = []

    def add_transition(self, kind: str, value, to_state: int):
        self.transitions.append(Transition(kind, value, to_state))

class NFA:
    def __init__(self, nfa_id: str):
        self.nfa_id = nfa_id
        self.states: dict[int, State] = {}
        self.start_state: int | None = None
        self.final_states: set[int] = set()

    def add_state(self, sid: int, is_final: bool = False):
        self.states[sid] = State(sid, is_final=is_final)
        if is_final:
            self.final_states.add(sid)

    def set_final(self, sid: int, is_final: bool):
        self.states[sid].is_final = is_final
        if is_final:
            self.final_states.add(sid)
        else:
            self.final_states.discard(sid)

    def add_transition(self, from_sid: int, kind: str, value, to_sid: int):
        self.states[from_sid].add_transition(kind, value, to_sid)

    @staticmethod
    def basic_range(nfa_id: str, low: str, high: str):
        nfa = NFA(nfa_id)
        nfa.add_state(0, is_final=False)
        nfa.add_state(1, is_final=True)
        nfa.start_state = 0
        nfa.add_transition(0, "range", (low, high), 1)
        return nfa

    def relabel_from(self, start_from: int):
        """
        Crea una copia del AFN con IDs de estados renumerados de forma consecutiva
        a partir de start_from. Retorna (nuevo_afn, next_id).
        """
        old_ids = sorted(self.states.keys())
        mapping = {old: start_from + i for i, old in enumerate(old_ids)}
        next_id = start_from + len(old_ids)

        new_nfa = NFA(self.nfa_id)
        for old in old_ids:
            new_nfa.add_state(mapping[old], is_final=self.states[old].is_final)

        new_nfa.start_state = mapping[self.start_state]

        # copiar transiciones
        for old in old_ids:
            src_new = mapping[old]
            for t in self.states[old].transitions:
                dst_new = mapping[t.to_state]
                new_nfa.add_transition(src_new, t.kind, t.value, dst_new)

        return new_nfa, next_id

    @staticmethod
    def union_thompson(nfa1, nfa2, new_id: str):
        """
        Unión (A|B) estilo Thompson:
        nuevo_start --ε--> start1
        nuevo_start --ε--> start2
        finals1 --ε--> nuevo_final
        finals2 --ε--> nuevo_final
        """
        res = NFA(new_id)

        # nuevo start = 0
        res.add_state(0, is_final=False)
        res.start_state = 0

        # copiar nfa1 renumerado desde 1
        c1, next_id = nfa1.relabel_from(1)

        # copiar nfa2 renumerado desde next_id
        c2, next_id = nfa2.relabel_from(next_id)

        # agregar estados de c1 y c2 a res
        for sid, st in c1.states.items():
            res.states[sid] = st
        for sid, st in c2.states.items():
            res.states[sid] = st

        # nuevo final
        new_final = next_id
        res.add_state(new_final, is_final=True)

        # ε desde nuevo start a starts
        res.add_transition(res.start_state, "epsilon", None, c1.start_state)
        res.add_transition(res.start_state, "epsilon", None, c2.start_state)

        # conectar finales viejos al nuevo final (y desmarcarlos como finales)
        for f in list(c1.final_states):
            res.add_transition(f, "epsilon", None, new_final)
            res.set_final(f, False)
        for f in list(c2.final_states):
            res.add_transition(f, "epsilon", None, new_final)
            res.set_final(f, False)

        res.final_states = {new_final}
        return res


# -----------------------------
# UI
# -----------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Constructor de AFN/AFD")
        self.geometry("1040x600")
        self.minsize(820, 480)
        self.configure(bg="white")

        self.afns: dict[str, NFA] = {}

        # Barra superior
        topbar = tk.Frame(self, bg="white", height=44)
        topbar.pack(side="top", fill="x")

        tk.Label(topbar, text="", bg="white").pack(side="left", padx=8)

        self.menu_btn = tk.Menubutton(
            topbar,
            text="AFN'S",
            bg="white",
            fg="black",
            relief="solid",
            borderwidth=1,
            padx=10,
            pady=6,
            activebackground="#f2f2f2",
            activeforeground="black",
            cursor="hand2"
        )
        self.menu_btn.pack(side="right", padx=12, pady=8)

        menu = tk.Menu(self.menu_btn, tearoff=0)
        self.menu_btn.configure(menu=menu)

        menu.add_command(label="Basicos (crear automata)", command=self.basicos_crear_automata)
        menu.add_separator()
        menu.add_command(label="Unir", command=self.unir)
        menu.add_command(label="Concatenar", command=self.concatenar)
        menu.add_command(label="Cerradura +", command=self.cerradura_mas)
        menu.add_command(label="Cerradura *", command=self.cerradura_estrella)
        menu.add_command(label="Opcional", command=self.opcional)
        menu.add_separator()
        menu.add_command(label="ER -> AFN", command=self.er_a_afn)
        menu.add_command(label="Union para Analizador Lexico", command=self.union_analizador_lexico)
        menu.add_command(label="Convertir AFN a AFD", command=self.afn_a_afd)
        menu.add_separator()
        menu.add_command(label="Analizar una Cadena", command=self.analizar_cadena)
        menu.add_command(label="Probar Analizador", command=self.probar_analizador)

        # Cuerpo
        body = tk.Frame(self, bg="white")
        body.pack(side="top", fill="both", expand=True)

        # Sidebar
        sidebar = tk.Frame(body, bg="white", width=260)
        sidebar.pack(side="left", fill="y", padx=(12, 6), pady=12)
        sidebar.pack_propagate(False)

        tk.Label(sidebar, text="AFNs guardados", bg="white", fg="black",
                 font=("Arial", 11, "bold")).pack(anchor="w")

        self.afn_listbox = tk.Listbox(
            sidebar,
            bg="white",
            fg="black",
            highlightthickness=1,
            highlightbackground="#e0e0e0",
            relief="flat"
        )
        self.afn_listbox.pack(fill="both", expand=True, pady=(8, 0))
        self.afn_listbox.bind("<<ListboxSelect>>", self.on_select_afn)

        # Área principal
        main = tk.Frame(body, bg="white")
        main.pack(side="left", fill="both", expand=True, padx=(6, 12), pady=12)

        self.canvas = tk.Canvas(main, bg="white", highlightthickness=1, highlightbackground="#e0e0e0")
        self.canvas.pack(fill="both", expand=True)

        self.canvas.create_text(
            340, 40,
            text="Crea AFNs desde el menú para verlos aquí.",
            fill="#666666",
            font=("Arial", 12)
        )

    # -----------------------------
    # Basicos (crear AFN rango)
    # -----------------------------
    def basicos_crear_automata(self):
        win = tk.Toplevel(self)
        win.title("AFN Básico")
        win.geometry("420x280")
        win.resizable(False, False)
        win.configure(bg="white")
        win.transient(self)
        win.grab_set()

        box = tk.LabelFrame(win, text="Crear AFN básico (rango de caracteres)", bg="white", fg="black")
        box.pack(fill="both", expand=True, padx=14, pady=14)

        tk.Label(box, text="Caracter Inferior:", bg="white").grid(row=0, column=0, sticky="w", padx=10, pady=(12, 6))
        low_entry = tk.Entry(box, width=10)
        low_entry.grid(row=0, column=1, sticky="w", padx=10, pady=(12, 6))

        tk.Label(box, text="Caracter Superior:", bg="white").grid(row=1, column=0, sticky="w", padx=10, pady=6)
        high_entry = tk.Entry(box, width=10)
        high_entry.grid(row=1, column=1, sticky="w", padx=10, pady=6)

        tk.Label(box, text="Ejemplo: A - Z", bg="white", fg="#666666").grid(row=2, column=1, sticky="w", padx=10, pady=(0, 10))

        tk.Label(box, text="ID del AFN:", bg="white").grid(row=3, column=0, sticky="w", padx=10, pady=6)
        id_entry = tk.Entry(box, width=18)
        id_entry.grid(row=3, column=1, sticky="w", padx=10, pady=6)

        btns = tk.Frame(box, bg="white")
        btns.grid(row=4, column=0, columnspan=2, sticky="e", padx=10, pady=16)

        def crear():
            low = low_entry.get().strip()
            high = high_entry.get().strip()
            nfa_id = id_entry.get().strip()

            if not nfa_id:
                messagebox.showerror("Error", "El ID del AFN no puede estar vacío.")
                return
            if nfa_id in self.afns:
                messagebox.showerror("Error", f"Ya existe un AFN con ID '{nfa_id}'.")
                return
            if len(low) != 1 or len(high) != 1:
                messagebox.showerror("Error", "Caracter Inferior y Superior deben ser un solo carácter.")
                return
            if ord(low) > ord(high):
                messagebox.showerror("Error", "El Caracter Inferior debe ser <= Caracter Superior.")
                return

            nfa = NFA.basic_range(nfa_id, low, high)
            self.afns[nfa_id] = nfa
            self.afn_listbox.insert(tk.END, nfa_id)

            self._select_id_in_listbox(nfa_id)
            self.draw_nfa(nfa)

            messagebox.showinfo("Listo", f"AFN '{nfa_id}' creado y guardado.")
            win.destroy()

        tk.Button(btns, text="Crear", command=crear, bg="white",
                  relief="solid", borderwidth=1, padx=12, pady=4).pack(side="right", padx=(8, 0))
        tk.Button(btns, text="Cancelar", command=win.destroy, bg="white",
                  relief="solid", borderwidth=1, padx=12, pady=4).pack(side="right")

        low_entry.focus_set()

    # -----------------------------
    # UNIR (A | B)
    # -----------------------------
    def unir(self):
        win = tk.Toplevel(self)
        win.title("Unir AFNs (A | B)")
        win.geometry("460x300")
        win.resizable(False, False)
        win.configure(bg="white")
        win.transient(self)
        win.grab_set()

        box = tk.LabelFrame(win, text="Unión de AFNs", bg="white", fg="black")
        box.pack(fill="both", expand=True, padx=14, pady=14)

        tk.Label(box, text="ID AFN 1:", bg="white").grid(row=0, column=0, sticky="w", padx=10, pady=(14, 6))
        id1_entry = tk.Entry(box, width=20)
        id1_entry.grid(row=0, column=1, sticky="w", padx=10, pady=(14, 6))

        tk.Label(box, text="ID AFN 2:", bg="white").grid(row=1, column=0, sticky="w", padx=10, pady=6)
        id2_entry = tk.Entry(box, width=20)
        id2_entry.grid(row=1, column=1, sticky="w", padx=10, pady=6)

        tk.Label(box, text="Nuevo ID (resultado):", bg="white").grid(row=2, column=0, sticky="w", padx=10, pady=6)
        new_id_entry = tk.Entry(box, width=20)
        new_id_entry.grid(row=2, column=1, sticky="w", padx=10, pady=6)

        # hint
        disponibles = ", ".join(self.afns.keys()) if self.afns else "(ninguno)"
        tk.Label(box, text=f"Disponibles: {disponibles}", bg="white", fg="#666666").grid(
            row=3, column=0, columnspan=2, sticky="w", padx=10, pady=(6, 0)
        )

        btns = tk.Frame(box, bg="white")
        btns.grid(row=4, column=0, columnspan=2, sticky="e", padx=10, pady=18)

        def hacer_union():
            id1 = id1_entry.get().strip()
            id2 = id2_entry.get().strip()
            new_id = new_id_entry.get().strip()

            if not id1 or not id2 or not new_id:
                messagebox.showerror("Error", "Debes llenar ID AFN 1, ID AFN 2 y Nuevo ID.")
                return
            if id1 == id2:
                messagebox.showerror("Error", "ID AFN 1 y ID AFN 2 deben ser distintos.")
                return
            if id1 not in self.afns:
                messagebox.showerror("Error", f"No existe el AFN con ID '{id1}'.")
                return
            if id2 not in self.afns:
                messagebox.showerror("Error", f"No existe el AFN con ID '{id2}'.")
                return
            if new_id in self.afns:
                messagebox.showerror("Error", f"Ya existe un AFN con ID '{new_id}'.")
                return

            nfa1 = self.afns[id1]
            nfa2 = self.afns[id2]

            # Crear unión
            res = NFA.union_thompson(nfa1, nfa2, new_id)

            # Borrar originales
            del self.afns[id1]
            del self.afns[id2]
            self._remove_id_from_listbox(id1)
            self._remove_id_from_listbox(id2)

            # Guardar nuevo
            self.afns[new_id] = res
            self.afn_listbox.insert(tk.END, new_id)
            self._select_id_in_listbox(new_id)

            # Dibujar
            self.draw_nfa(res)

            messagebox.showinfo("Listo", f"Se unieron '{id1}' y '{id2}' → nuevo AFN '{new_id}'.\nLos AFNs originales fueron eliminados.")
            win.destroy()

        tk.Button(btns, text="Unir", command=hacer_union, bg="white",
                  relief="solid", borderwidth=1, padx=12, pady=4).pack(side="right", padx=(8, 0))
        tk.Button(btns, text="Cancelar", command=win.destroy, bg="white",
                  relief="solid", borderwidth=1, padx=12, pady=4).pack(side="right")

        id1_entry.focus_set()

    # -----------------------------
    # Dibujado general en Canvas
    # -----------------------------
    def draw_nfa(self, nfa: NFA):
        self.canvas.delete("all")
        self.update_idletasks()

        w = max(self.canvas.winfo_width(), 600)
        h = max(self.canvas.winfo_height(), 400)

        # Título
        self.canvas.create_text(20, 18, anchor="w", text=f"AFN: {nfa.nfa_id}", fill="black", font=("Arial", 12, "bold"))

        # BFS para niveles
        start = nfa.start_state
        levels = {start: 0}
        order_in_level = {0: [start]}
        q = [start]
        visited = set([start])

        while q:
            u = q.pop(0)
            lu = levels[u]
            for t in nfa.states[u].transitions:
                v = t.to_state
                if v not in visited:
                    visited.add(v)
                    levels[v] = lu + 1
                    order_in_level.setdefault(lu + 1, []).append(v)
                    q.append(v)

        # estados no alcanzables (por si acaso)
        for sid in sorted(nfa.states.keys()):
            if sid not in levels:
                lvl = max(levels.values(), default=0) + 1
                levels[sid] = lvl
                order_in_level.setdefault(lvl, []).append(sid)

        max_level = max(order_in_level.keys(), default=0)

        # layout
        left_margin = 120
        top_margin = 70
        x_gap = 170
        r = 28

        # ajustar gap si se sale
        needed_w = left_margin + (max_level * x_gap) + 220
        if needed_w > w:
            x_gap = max(120, int((w - left_margin - 220) / max(1, max_level)))

        positions = {}
        for lvl in range(0, max_level + 1):
            nodes = order_in_level.get(lvl, [])
            if not nodes:
                continue
            # espaciado vertical
            y_gap = 120
            total_h = (len(nodes) - 1) * y_gap
            start_y = top_margin + max(0, (h - top_margin - total_h) // 2 - 40)

            if start_y < top_margin:
                start_y = top_margin
                # comprimir si hay muchos
                if len(nodes) > 1:
                    y_gap = max(70, int((h - top_margin - 80) / (len(nodes) - 1)))

            x = left_margin + lvl * x_gap
            for i, sid in enumerate(nodes):
                y = start_y + i * y_gap
                positions[sid] = (x, y)

        # Flecha de inicio
        sx, sy = positions[start]
        self.canvas.create_line(sx - 90, sy, sx - r, sy, arrow=tk.LAST, width=2)
        self.canvas.create_text(sx - 100, sy - 16, text="start", fill="#555555", font=("Arial", 10))

        # Dibujar estados
        for sid, (x, y) in positions.items():
            is_final = sid in nfa.final_states
            self._draw_state(x, y, r, str(sid), is_final)

        # Dibujar transiciones
        for sid, st in nfa.states.items():
            x1, y1 = positions[sid]
            for idx, t in enumerate(st.transitions):
                dst = t.to_state
                x2, y2 = positions[dst]
                label = t.label()

                if sid == dst:
                    # self-loop
                    loop_r = r + 16
                    self.canvas.create_arc(
                        x1 - loop_r, y1 - loop_r - 10, x1 + loop_r, y1 + loop_r - 10,
                        start=30, extent=300, style="arc", width=2
                    )
                    self.canvas.create_text(x1, y1 - loop_r - 18, text=label, fill="black", font=("Arial", 10))
                    continue

                # línea directa o curva si va "hacia atrás"
                if x2 >= x1:
                    self.canvas.create_line(x1 + r, y1, x2 - r, y2, arrow=tk.LAST, width=2)
                    mx, my = (x1 + x2) / 2, (y1 + y2) / 2
                    self.canvas.create_text(mx, my - 14, text=label, fill="black", font=("Arial", 10))
                else:
                    # back-edge curvada arriba
                    ctrl_x = (x1 + x2) / 2
                    ctrl_y = min(y1, y2) - (60 + 18 * (idx % 3))
                    self.canvas.create_line(
                        x1 - r, y1,
                        ctrl_x, ctrl_y,
                        x2 + r, y2,
                        smooth=True,
                        arrow=tk.LAST,
                        width=2
                    )
                    self.canvas.create_text(ctrl_x, ctrl_y - 12, text=label, fill="black", font=("Arial", 10))

    def _draw_state(self, x, y, r, text, is_final=False):
        self.canvas.create_oval(x - r, y - r, x + r, y + r, width=2)
        if is_final:
            self.canvas.create_oval(x - r + 6, y - r + 6, x + r - 6, y + r - 6, width=2)
        self.canvas.create_text(x, y, text=text, fill="black", font=("Arial", 11, "bold"))

    # -----------------------------
    # Helpers para Listbox
    # -----------------------------
    def _remove_id_from_listbox(self, nfa_id: str):
        items = self.afn_listbox.get(0, tk.END)
        for i, item in enumerate(items):
            if item == nfa_id:
                self.afn_listbox.delete(i)
                return

    def _select_id_in_listbox(self, nfa_id: str):
        items = self.afn_listbox.get(0, tk.END)
        for i, item in enumerate(items):
            if item == nfa_id:
                self.afn_listbox.selection_clear(0, tk.END)
                self.afn_listbox.selection_set(i)
                self.afn_listbox.activate(i)
                return

    def on_select_afn(self, _evt):
        sel = self.afn_listbox.curselection()
        if not sel:
            return
        nfa_id = self.afn_listbox.get(sel[0])
        nfa = self.afns.get(nfa_id)
        if nfa:
            self.draw_nfa(nfa)

    # -----------------------------
    # Placeholders restantes
    # -----------------------------
    def concatenar(self):
        messagebox.showinfo("AFN/AFD", "Concatenar - pendiente de implementar.")

    def cerradura_mas(self):
        messagebox.showinfo("AFN/AFD", "Cerradura + - pendiente de implementar.")

    def cerradura_estrella(self):
        messagebox.showinfo("AFN/AFD", "Cerradura * - pendiente de implementar.")

    def opcional(self):
        messagebox.showinfo("AFN/AFD", "Opcional - pendiente de implementar.")

    def er_a_afn(self):
        messagebox.showinfo("AFN/AFD", "ER -> AFN - pendiente de implementar.")

    def union_analizador_lexico(self):
        messagebox.showinfo("AFN/AFD", "Union para Analizador Lexico - pendiente de implementar.")

    def afn_a_afd(self):
        messagebox.showinfo("AFN/AFD", "Convertir AFN a AFD - pendiente de implementar.")

    def analizar_cadena(self):
        messagebox.showinfo("AFN/AFD", "Analizar una Cadena - pendiente de implementar.")

    def probar_analizador(self):
        messagebox.showinfo("AFN/AFD", "Probar Analizador - pendiente de implementar.")


if __name__ == "__main__":
    app = App()
    app.mainloop()