import itertools
import json

def solve():
    houses = [0, 1, 2, 3]  # 0-based indices for houses 1..4

    categories = ["Name", "Mother", "Smoothie", "Height", "Education"]

    values = {
        "Name": ["Peter", "Alice", "Eric", "Arnold"],
        "Mother": ["Janelle", "Holly", "Aniya", "Kailyn"],
        "Smoothie": ["watermelon", "dragonfruit", "desert", "cherry"],
        "Height": ["tall", "average", "short", "very short"],
        "Education": ["high school", "associate", "master", "bachelor"],
    }

    # Helper: generate permutations with basic unary pre-filters from the clues
    def generate_candidates():
        cand = {}

        # Mother: Janelle is in the third house (index 2)
        moms = values["Mother"]
        cand_mother = []
        for perm in itertools.permutations(moms):
            if perm[2] == "Janelle":
                cand_mother.append(perm)
        cand["Mother"] = cand_mother

        # Height: tall is at house 3 (index 2); plus partial constraints:
        # - short cannot be at index 0 because dragonfruit must be left of short
        # - very short cannot be at index 3 because must be left of high school
        # - average cannot be at index 3 because someone must be to the right of average (Arnold)
        heights = values["Height"]
        cand_height = []
        for perm in itertools.permutations(heights):
            if perm[2] != "tall":
                continue
            if perm.index("short") == 0:
                continue
            if perm.index("very short") == 3:
                continue
            if perm.index("average") == 3:
                continue
            cand_height.append(perm)
        cand["Height"] = cand_height

        # Name: Alice is tall -> Alice is at house 3 (index 2)
        names = values["Name"]
        cand_name = []
        for perm in itertools.permutations(names):
            if perm[2] == "Alice":
                cand_name.append(perm)
        cand["Name"] = cand_name

        # Smoothie: desert not in first house (index 0), dragonfruit cannot be at last house (index 3)
        smoothies = values["Smoothie"]
        cand_smoothie = []
        for perm in itertools.permutations(smoothies):
            if perm[0] == "desert":
                continue
            if perm[3] == "dragonfruit":
                continue
            cand_smoothie.append(perm)
        cand["Smoothie"] = cand_smoothie

        # Education: high school not in third house (index 2) and must have a left position for very short -> not index 0 either
        # So high school can only be at indices 1 or 3.
        educs = values["Education"]
        cand_edu = []
        for perm in itertools.permutations(educs):
            hs_idx = perm.index("high school")
            if hs_idx in (0, 2):
                continue
            cand_edu.append(perm)
        cand["Education"] = cand_edu

        return cand

    candidates = generate_candidates()

    # Constraint checker
    def is_valid(assign):
        # Helper to get index if known
        def pos(cat, val):
            arr = assign.get(cat)
            if arr is None:
                return None
            return arr.index(val)

        # Clue 1: Janelle in the third house
        m = assign.get("Mother")
        if m is not None:
            if m[2] != "Janelle":
                return False

        # Clue 9: Tall is Janelle (same person)
        h = assign.get("Height")
        if h is not None:
            if h[2] != "tall":
                return False  # also from clue 12 and 1, tall at 3
        if m is not None and h is not None:
            if pos("Height", "tall") != pos("Mother", "Janelle"):
                return False

        # Clue 12: Tall is Alice (same person)
        n = assign.get("Name")
        if n is not None and h is not None:
            if pos("Name", "Alice") != pos("Height", "tall"):
                return False

        # Clue 2: Desert <-> master (same person)
        s = assign.get("Smoothie")
        e = assign.get("Education")
        if s is not None and e is not None:
            if pos("Smoothie", "desert") != pos("Education", "master"):
                return False

        # Clue 3: Desert not in first house
        if s is not None:
            if s[0] == "desert":
                return False

        # Clue 4: very short is left of high school
        if h is not None and e is not None:
            if pos("Height", "very short") >= pos("Education", "high school"):
                return False
        # Partial implications for clue 4 (already filtered in candidates but keep for safety)
        if h is not None:
            if h.index("very short") == 3:
                return False
        if e is not None:
            if e.index("high school") in (0, 2):  # 0 invalid due to "left of", 2 invalid by clue 6
                return False

        # Clue 5: Eric and Cherry are next to each other
        if n is not None and s is not None:
            if abs(pos("Name", "Eric") - pos("Smoothie", "cherry")) != 1:
                return False

        # Clue 6: High school not in third house
        if e is not None:
            if e[2] == "high school":
                return False

        # Clue 7: Kailyn <-> associate
        if m is not None and e is not None:
            if pos("Mother", "Kailyn") != pos("Education", "associate"):
                return False

        # Clue 8: Cherry <-> Aniya
        if s is not None and m is not None:
            if pos("Smoothie", "cherry") != pos("Mother", "Aniya"):
                return False

        # Clue 10: Arnold is to the right of average
        if n is not None and h is not None:
            if not (pos("Name", "Arnold") > pos("Height", "average")):
                return False
        # Partial: average cannot be at the far right (index 3)
        if h is not None:
            if h.index("average") == 3:
                return False

        # Clue 11: Dragonfruit directly left of short
        if s is not None and h is not None:
            if pos("Smoothie", "dragonfruit") + 1 != pos("Height", "short"):
                return False
        # Partial: dragonfruit cannot be at the last position
        if s is not None:
            if s.index("dragonfruit") == 3:
                return False
        # Partial: short cannot be at the first position
        if h is not None:
            if h.index("short") == 0:
                return False

        return True

    order = ["Mother", "Height", "Name", "Smoothie", "Education"]

    solution = {}

    def backtrack(i, current):
        nonlocal solution
        if i == len(order):
            if is_valid(current):
                solution = {k: list(v) for k, v in current.items()}
                return True
            return False

        cat = order[i]
        for perm in candidates[cat]:
            current[cat] = perm
            if is_valid(current):
                if backtrack(i + 1, current):
                    return True
            current[cat] = None
        return False

    # Initialize current assignment
    current = {cat: None for cat in categories}
    found = backtrack(0, current)

    if not found:
        raise RuntimeError("No solution found for the given puzzle.")

    # Build output
    header = ["House", "Name", "Mother", "Smoothie", "Height", "Education"]
    rows = []
    for i in range(4):
        row = [
            str(i + 1),
            solution["Name"][i],
            solution["Mother"][i],
            solution["Smoothie"][i],
            solution["Height"][i],
            solution["Education"][i],
        ]
        rows.append(row)

    out = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return out

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result))