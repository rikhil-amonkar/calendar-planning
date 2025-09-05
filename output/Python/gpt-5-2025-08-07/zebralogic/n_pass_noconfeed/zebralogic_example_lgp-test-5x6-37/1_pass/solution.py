import json
from copy import deepcopy

def solve_puzzle():
    # Domains
    Names = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
    Hobbies = ["cooking", "gardening", "painting", "photography", "knitting"]
    Sports = ["swimming", "tennis", "soccer", "baseball", "basketball"]
    Styles = ["ranch", "craftsman", "victorian", "modern", "colonial"]
    Children = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
    Heights = ["average", "very tall", "very short", "short", "tall"]

    CATS = ["Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"]
    DOMAIN = {
        "Name": Names,
        "Hobby": Hobbies,
        "FavoriteSport": Sports,
        "HouseStyle": Styles,
        "Children": Children,
        "Height": Heights,
    }

    # State structure
    state = {
        "Name": [None]*5,
        "Hobby": [None]*5,
        "FavoriteSport": [None]*5,
        "HouseStyle": [None]*5,
        "Children": [None]*5,
        "Height": [None]*5,
        "remaining": {
            "Name": set(Names),
            "Hobby": set(Hobbies),
            "FavoriteSport": set(Sports),
            "HouseStyle": set(Styles),
            "Children": set(Children),
            "Height": set(Heights),
        }
    }

    # Equality groups mapping (within the same house)
    # Build equivalence map such that assigning any (cat,val) enforces other linked pairs in the same house.
    eq_map = {}

    def add_group(pairs):
        for i in range(len(pairs)):
            a = pairs[i]
            others = [pairs[j] for j in range(len(pairs)) if j != i]
            eq_map.setdefault(a, [])
            for o in others:
                if o not in eq_map[a]:
                    eq_map[a].append(o)

    # Groups:
    # Bob <-> painting
    add_group([("Name", "Bob"), ("Hobby", "painting")])
    # Peter <-> very tall <-> baseball
    add_group([("Name", "Peter"), ("Height", "very tall"), ("FavoriteSport", "baseball")])
    # short <-> basketball
    add_group([("Height", "short"), ("FavoriteSport", "basketball")])
    # average <-> craftsman <-> Meredith
    add_group([("Height", "average"), ("HouseStyle", "craftsman"), ("Children", "Meredith")])
    # tennis <-> Samantha <-> modern <-> cooking
    add_group([("FavoriteSport", "tennis"), ("Children", "Samantha"), ("HouseStyle", "modern"), ("Hobby", "cooking")])
    # victorian <-> Fred
    add_group([("HouseStyle", "victorian"), ("Children", "Fred")])
    # Alice <-> tall
    add_group([("Name", "Alice"), ("Height", "tall")])

    # Utility for reversible assignments
    def assign_single(st, cat, house, value, changes):
        # Assign a single slot without auto-propagation, record changes
        current = st[cat][house]
        if current is not None:
            if current != value:
                return False
            return True
        # Ensure value available
        if value not in st["remaining"][cat]:
            return False
        # Set value
        st[cat][house] = value
        changes.append(("set", cat, house, None))
        # Remove from remaining
        st["remaining"][cat].remove(value)
        changes.append(("remove_remaining", cat, value))
        return True

    def propagate_equalities(st, house, changes):
        # Process all equalities within this house until no new info
        queue = []
        seen = set()
        # seed queue with all assigned pairs at this house
        for cat in CATS:
            val = st[cat][house]
            if val is not None:
                queue.append((cat, val))

        while queue:
            cat, val = queue.pop()
            key = (cat, val)
            if key in seen:
                continue
            seen.add(key)
            if key in eq_map:
                for (cat2, val2) in eq_map[key]:
                    # Assign implied value in same house
                    if st[cat2][house] is None:
                        if not assign_single(st, cat2, house, val2, changes):
                            return False
                        # Newly assigned, may imply more
                        queue.append((cat2, val2))
                    else:
                        if st[cat2][house] != val2:
                            return False
        return True

    def assign_with_propagation(st, cat, house, value, changes):
        if not assign_single(st, cat, house, value, changes):
            return False
        if not propagate_equalities(st, house, changes):
            return False
        return True

    def undo_changes(st, changes):
        # Revert in reverse order
        for entry in reversed(changes):
            typ = entry[0]
            if typ == "set":
                _, cat, house, prev = entry
                st[cat][house] = prev
            elif typ == "remove_remaining":
                _, cat, value = entry
                st["remaining"][cat].add(value)

    # Constraint checks
    def check_partial(st):
        names = st["Name"]
        hobbies = st["Hobby"]
        sports = st["FavoriteSport"]
        styles = st["HouseStyle"]
        children = st["Children"]
        heights = st["Height"]

        # 20: Victorian is in the fifth house (index 4)
        if styles[4] is not None and styles[4] != "victorian":
            return False
        # If Victorian assigned elsewhere, fail
        for i in range(4):
            if styles[i] == "victorian":
                return False

        # 3: Peter directly left of Victorian
        # If Victorian known at v (must be 4), then house v-1 must be Peter
        v = 4  # fixed by clue 20
        left = v - 1
        # If Peter assigned and not at left, fail
        if any(n == "Peter" for n in names if n is not None):
            p_idx = None
            for i, n in enumerate(names):
                if n == "Peter":
                    p_idx = i
                    break
            if p_idx is not None:
                if p_idx != left:
                    return False
                # also ensure right neighbor of Peter is Victorian
                if styles[p_idx + 1] is not None and styles[p_idx + 1] != "victorian":
                    return False
        # Also if left house name assigned and not Peter, fail
        if names[left] is not None and names[left] != "Peter":
            return False

        # 2: Tall is in the second house
        if heights[1] is not None and heights[1] != "tall":
            return False
        # Tall appears nowhere else
        for i in [0,2,3,4]:
            if heights[i] == "tall":
                return False

        # 8: Gardening is in the second house
        if hobbies[1] is not None and hobbies[1] != "gardening":
            return False
        for i in [0,2,3,4]:
            if hobbies[i] == "gardening":
                return False

        # 11: Soccer is not in the first house
        if sports[0] == "soccer":
            return False

        # 18: Knitting and gardening are next to each other.
        # Since gardening is fixed at house 2 (index 1), knitting must be at index 0 or 2.
        # If knitting assigned and not at 0 or 2, fail.
        for i, h in enumerate(hobbies):
            if h == "knitting" and i not in (0,2):
                return False
        # If both positions 0 and 2 are assigned to non-knitting and knitting not yet assigned anywhere, fail
        if "knitting" in st["remaining"]["Hobby"]:
            cond0 = (hobbies[0] is not None and hobbies[0] != "knitting")
            cond2 = (hobbies[2] is not None and hobbies[2] != "knitting")
            if cond0 and cond2:
                return False

        # 6: Meredith and Timothy are next to each other.
        # Check when both assigned
        m_idx = None
        t_idx = None
        for i, c in enumerate(children):
            if c == "Meredith":
                m_idx = i
            if c == "Timothy":
                t_idx = i
        if m_idx is not None and t_idx is not None:
            if abs(m_idx - t_idx) != 1:
                return False
        elif m_idx is not None and t_idx is None:
            # Ensure Meredith has at least one neighbor that could be Timothy
            neighbors = []
            if m_idx - 1 >= 0:
                neighbors.append(m_idx - 1)
            if m_idx + 1 <= 4:
                neighbors.append(m_idx + 1)
            possible = False
            for j in neighbors:
                if children[j] is None or children[j] == "Timothy":
                    possible = True
                    break
            if not possible:
                return False
        elif t_idx is not None and m_idx is None:
            neighbors = []
            if t_idx - 1 >= 0:
                neighbors.append(t_idx - 1)
            if t_idx + 1 <= 4:
                neighbors.append(t_idx + 1)
            possible = False
            for j in neighbors:
                if children[j] is None or children[j] == "Meredith":
                    possible = True
                    break
            if not possible:
                return False

        # 9: very short is somewhere to the right of Eric.
        vs_idx = None
        eric_idx = None
        for i, h in enumerate(heights):
            if h == "very short":
                vs_idx = i
        for i, n in enumerate(names):
            if n == "Eric":
                eric_idx = i
        if vs_idx is not None and eric_idx is not None:
            if not (vs_idx > eric_idx):
                return False
        else:
            # Partial feasibility checks
            if eric_idx is not None and vs_idx is None:
                # ensure there exists some j > eric_idx where very short could still go
                possible = False
                for j in range(eric_idx + 1, 5):
                    if heights[j] is None or heights[j] == "very short":
                        possible = True
                        break
                if not possible:
                    return False
            if vs_idx is not None and eric_idx is None:
                # ensure there exists some i < vs_idx where Eric could go
                possible = False
                for i in range(0, vs_idx):
                    if names[i] is None or names[i] == "Eric":
                        possible = True
                        break
                if not possible:
                    return False

        # 17: The ranch is somewhere to the left of cooking.
        # But cooking is bound to modern/tennis/Samantha by equalities.
        ranch_idx = None
        cook_idx = None
        for i, s in enumerate(styles):
            if s == "ranch":
                ranch_idx = i
        for i, h in enumerate(hobbies):
            if h == "cooking":
                cook_idx = i
        if ranch_idx is not None and cook_idx is not None:
            if not (ranch_idx < cook_idx):
                return False
        elif ranch_idx is not None and cook_idx is None:
            # ensure there exists some j > ranch_idx that could still be cooking
            possible = False
            for j in range(ranch_idx + 1, 5):
                if hobbies[j] is None or hobbies[j] == "cooking":
                    possible = True
                    break
            if not possible:
                return False
        elif ranch_idx is None and cook_idx is not None:
            # ensure there exists some i < cook_idx that could still be ranch
            possible = False
            for i in range(0, cook_idx):
                if styles[i] is None or styles[i] == "ranch":
                    possible = True
                    break
            if not possible:
                return False

        # 3 general: Peter must have someone to his right (Victorian), so Peter cannot be at last house
        if "Peter" in names:
            p = names.index("Peter")
            if p == 4:
                return False
            if styles[p+1] is not None and styles[p+1] != "victorian":
                return False

        # 12 + 19: Child Samantha <-> modern <-> cooking ensured by equality mapping; no extra check needed

        # 1 + 13: Average <-> Craftsman <-> Meredith ensured by equality mapping

        # 5 + 16 + group: Very tall <-> baseball <-> Peter ensured by equality mapping

        # 15: short <-> basketball ensured by equality mapping

        # Final uniqueness is managed by remaining sets

        return True

    def all_assigned(st):
        for cat in CATS:
            if any(v is None for v in st[cat]):
                return False
        return True

    # MRV heuristic: choose the next (cat, house) with minimal viable candidate count
    def get_candidates_for_slot(st, cat, house):
        candidates = []
        for val in sorted(st["remaining"][cat]):
            changes = []
            ok = assign_with_propagation(st, cat, house, val, changes)
            if ok and check_partial(st):
                candidates.append((val, changes))
            # Undo trial
            undo_changes(st, changes)
        return candidates

    def select_next_slot(st):
        best = None
        best_candidates = None
        # Iterate over all unfilled slots
        for house in range(5):
            for cat in CATS:
                if st[cat][house] is None:
                    candidates = get_candidates_for_slot(st, cat, house)
                    if len(candidates) == 0:
                        return (cat, house, candidates)  # immediate failure
                    if best is None or len(candidates) < len(best_candidates):
                        best = (cat, house)
                        best_candidates = candidates
                        if len(best_candidates) == 1:
                            return (best[0], best[1], best_candidates)
        if best is None:
            return None
        return (best[0], best[1], best_candidates)

    def search(st):
        if not check_partial(st):
            return False
        if all_assigned(st):
            return True
        sel = select_next_slot(st)
        if sel is None:
            return False
        cat, house, candidates = sel
        if len(candidates) == 0:
            return False
        # Try each candidate (val), but we already know they pass partial check in isolation
        for (val, prepared_changes) in candidates:
            # Re-apply the same changes to move forward
            changes = []
            # Apply the candidate again (we must reassign because we undid after probing)
            ok = assign_with_propagation(st, cat, house, val, changes)
            if not ok or not check_partial(st):
                undo_changes(st, changes)
                continue
            if search(st):
                return True
            undo_changes(st, changes)
        return False

    # Apply initial fixed constraints with propagation:

    # 20: Victorian at house 5 (index 4)
    initial_changes = []
    if not assign_with_propagation(state, "HouseStyle", 4, "victorian", initial_changes):
        undo_changes(state, initial_changes)
        raise RuntimeError("Failed initial assignment for Victorian.")
    # 3 + 20: Peter is directly left of the Victorian -> house 4 (index 3)
    if not assign_with_propagation(state, "Name", 3, "Peter", initial_changes):
        undo_changes(state, initial_changes)
        raise RuntimeError("Failed initial assignment for Peter.")

    # 2: Tall is in the second house (index 1)
    if not assign_with_propagation(state, "Height", 1, "tall", initial_changes):
        undo_changes(state, initial_changes)
        raise RuntimeError("Failed initial assignment for Tall in house 2.")

    # 8: Gardening is in the second house (index 1)
    if not assign_with_propagation(state, "Hobby", 1, "gardening", initial_changes):
        undo_changes(state, initial_changes)
        raise RuntimeError("Failed initial assignment for Gardening in house 2.")

    # Now search
    if not search(state):
        raise RuntimeError("No solution found")

    # Build JSON solution
    header = ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"]
    rows = []
    for i in range(5):
        rows.append([
            str(i+1),
            state["Name"][i],
            state["Hobby"][i],
            state["FavoriteSport"][i],
            state["HouseStyle"][i],
            state["Children"][i],
            state["Height"][i],
        ])

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))