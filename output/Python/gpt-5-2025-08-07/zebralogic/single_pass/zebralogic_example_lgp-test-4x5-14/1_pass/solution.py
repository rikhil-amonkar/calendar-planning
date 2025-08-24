import json

def solve():
    houses = [
        {"Name": None, "Mother": None, "Smoothie": None, "Height": None, "Education": None}
        for _ in range(4)
    ]

    categories = ["Name", "Mother", "Smoothie", "Height", "Education"]

    values = {
        "Name": ["Peter", "Alice", "Eric", "Arnold"],
        "Mother": ["Janelle", "Holly", "Aniya", "Kailyn"],
        "Smoothie": ["watermelon", "dragonfruit", "desert", "cherry"],
        "Height": ["tall", "average", "short", "very short"],
        "Education": ["high school", "associate", "master", "bachelor"],
    }

    used = {cat: set() for cat in categories}

    # Pre-assign from clues:
    # 1. Janelle is in the third house.
    houses[2]["Mother"] = "Janelle"; used["Mother"].add("Janelle")
    # 9. Tall is Janelle's child -> in house 3.
    houses[2]["Height"] = "tall"; used["Height"].add("tall")
    # 12. Tall is Alice -> Alice in house 3.
    houses[2]["Name"] = "Alice"; used["Name"].add("Alice")

    def pos_of(cat, val):
        for i in range(4):
            if houses[i][cat] == val:
                return i
        return None

    def check_same_person(cat1, val1, cat2, val2):
        p1 = pos_of(cat1, val1)
        p2 = pos_of(cat2, val2)
        if p1 is not None and p2 is not None and p1 != p2:
            return False
        # Also if one side is assigned in a house, ensure the other side not conflicting in that house
        # (This is implicitly handled by the above and domain filtering)
        return True

    def check_constraints():
        # 1. Janelle in third house
        p = pos_of("Mother", "Janelle")
        if p is not None and p != 2:
            return False
        if houses[2]["Mother"] is not None and houses[2]["Mother"] != "Janelle":
            return False

        # 2. Desert <-> master
        if not check_same_person("Smoothie", "desert", "Education", "master"):
            return False

        # 3. Desert not in first house (index 0), hence master not in first either
        if houses[0]["Smoothie"] == "desert":
            return False
        if houses[0]["Education"] == "master":
            return False

        # 4. very short is left of high school
        vpos = pos_of("Height", "very short")
        hpos = pos_of("Education", "high school")
        if vpos is not None and hpos is not None:
            if not (vpos < hpos):
                return False
        # Simple boundary pruning
        if vpos == 3:
            return False
        if hpos == 0:
            return False

        # 5. Eric and Cherry adjacent
        epos = pos_of("Name", "Eric")
        cpos = pos_of("Smoothie", "cherry")
        if epos is not None and cpos is not None:
            if abs(epos - cpos) != 1:
                return False
        # Boundary adjacency pruning
        if epos == 0 and cpos is not None and cpos != 1:
            return False
        if epos == 3 and cpos is not None and cpos != 2:
            return False
        if cpos == 0 and epos is not None and epos != 1:
            return False
        if cpos == 3 and epos is not None and epos != 2:
            return False

        # 6. High school not in the third house
        if houses[2]["Education"] == "high school":
            return False

        # 7. Kailyn <-> associate
        if not check_same_person("Mother", "Kailyn", "Education", "associate"):
            return False

        # 8. Cherry <-> Aniya
        if not check_same_person("Smoothie", "cherry", "Mother", "Aniya"):
            return False

        # 9. Tall <-> Janelle
        if not check_same_person("Height", "tall", "Mother", "Janelle"):
            return False

        # 10. Arnold is somewhere to the right of average
        apos = pos_of("Name", "Arnold")
        avgpos = pos_of("Height", "average")
        if apos is not None and avgpos is not None:
            if not (apos > avgpos):
                return False

        # 11. Dragonfruit directly left of short
        dpos = pos_of("Smoothie", "dragonfruit")
        spos = pos_of("Height", "short")
        if dpos is not None and spos is not None:
            if dpos + 1 != spos:
                return False
        # Partial boundary pruning
        if dpos == 3:
            return False
        if spos == 0:
            return False

        # 12. Tall <-> Alice
        if not check_same_person("Height", "tall", "Name", "Alice"):
            return False

        return True

    def domain_for(i, cat):
        # start with unused values
        dom = [v for v in values[cat] if v not in used[cat]]

        # Hard domain pruning from explicit house-based constraints
        if cat == "Mother":
            # Janelle only in house 3
            if i == 2:
                dom = [v for v in dom if v == "Janelle"]
            else:
                dom = [v for v in dom if v != "Janelle"]
        if cat == "Height":
            # Tall only at house 3
            if i == 2:
                dom = [v for v in dom if v == "tall"]
            else:
                dom = [v for v in dom if v != "tall"]
            # Short cannot be in house 1 due to dragonfruit-left-of-short
            if i == 0:
                dom = [v for v in dom if v != "short"]
        if cat == "Name":
            # Alice only at house 3
            if i == 2:
                dom = [v for v in dom if v == "Alice"]
            else:
                dom = [v for v in dom if v != "Alice"]
        if cat == "Smoothie":
            # Desert not in house 1
            if i == 0:
                dom = [v for v in dom if v != "desert"]
            # Dragonfruit cannot be at house 4 due to being directly left of short
            if i == 3:
                dom = [v for v in dom if v != "dragonfruit"]
        if cat == "Education":
            # High school not at house 3
            if i == 2:
                dom = [v for v in dom if v != "high school"]
            # Master not in house 1 (since tied to desert)
            if i == 0:
                dom = [v for v in dom if v != "master"]

        # Pairwise link consistency within the same house
        filtered = []
        for v in dom:
            ok = True
            if cat == "Mother":
                if v == "Kailyn":
                    if houses[i]["Education"] is not None and houses[i]["Education"] != "associate":
                        ok = False
                if v == "Aniya":
                    if houses[i]["Smoothie"] is not None and houses[i]["Smoothie"] != "cherry":
                        ok = False
            if cat == "Education":
                if v == "associate":
                    if houses[i]["Mother"] is not None and houses[i]["Mother"] != "Kailyn":
                        ok = False
                if v == "master":
                    if houses[i]["Smoothie"] is not None and houses[i]["Smoothie"] != "desert":
                        ok = False
            if cat == "Smoothie":
                if v == "desert":
                    if houses[i]["Education"] is not None and houses[i]["Education"] != "master":
                        ok = False
                if v == "cherry":
                    if houses[i]["Mother"] is not None and houses[i]["Mother"] != "Aniya":
                        ok = False
            if cat == "Height":
                if v == "tall":
                    if houses[i]["Name"] is not None and houses[i]["Name"] != "Alice":
                        ok = False
                    if houses[i]["Mother"] is not None and houses[i]["Mother"] != "Janelle":
                        ok = False
            if cat == "Name":
                if v == "Alice":
                    if i != 2:
                        ok = False
                    if houses[i]["Height"] is not None and houses[i]["Height"] != "tall":
                        ok = False
            if ok:
                filtered.append(v)
        return filtered

    def select_unassigned():
        best = None
        best_dom = None
        for i in range(4):
            for cat in categories:
                if houses[i][cat] is None:
                    dom = domain_for(i, cat)
                    if best is None or len(dom) < len(best_dom):
                        best = (i, cat)
                        best_dom = dom
                        if len(dom) == 0:
                            return best, dom
        return best, best_dom

    def solve_rec():
        # if all assigned return True
        done = True
        for i in range(4):
            for cat in categories:
                if houses[i][cat] is None:
                    done = False
                    break
            if not done:
                break
        if done:
            return check_constraints()

        (i, cat), dom = select_unassigned()
        if dom is None:
            return False
        for v in dom:
            # assign
            houses[i][cat] = v
            used[cat].add(v)
            if check_constraints():
                if solve_rec():
                    return True
            # revert
            houses[i][cat] = None
            used[cat].remove(v)
        return False

    solved = solve_rec()
    if not solved:
        raise RuntimeError("No solution found")

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
            "rows": []
        }
    }
    for idx in range(4):
        row = [
            str(idx + 1),
            houses[idx]["Name"],
            houses[idx]["Mother"],
            houses[idx]["Smoothie"],
            houses[idx]["Height"],
            houses[idx]["Education"],
        ]
        result["solution"]["rows"].append(row)
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, indent=2))