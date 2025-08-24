import json
from typing import Dict, List, Optional, Set, Tuple

def solve_puzzle():
    # Categories and values
    categories = {
        "Name": ["Eric", "Peter", "Arnold", "Alice", "Bob"],
        "Food": ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"],
        "CarModel": ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"],
        "PhoneModel": ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"],
        "Occupation": ["teacher", "lawyer", "doctor", "artist", "engineer"],
        "Drink": ["tea", "milk", "water", "root beer", "coffee"],
    }

    # Build mapping from value -> category
    value_to_category = {}
    for cat, vals in categories.items():
        for v in vals:
            value_to_category[v] = cat

    # All values list
    all_values = []
    for vals in categories.values():
        all_values.extend(vals)

    # Constraint representations
    eq_pairs: List[Tuple[str, str]] = []
    left_of_pairs: List[Tuple[str, str]] = []        # x is somewhere left of y (x < y)
    next_left_pairs: List[Tuple[str, str]] = []      # x is immediately left of y (x = y - 1)
    dist_pairs: List[Tuple[str, str, int]] = []      # |pos(x) - pos(y)| == n
    not_pos: List[Tuple[str, int]] = []              # value not in house index
    abs_pos: List[Tuple[str, int]] = []              # value exactly in house index

    # Helper to add equality (same house)
    def add_eq(a, b):
        eq_pairs.append((a, b))

    # Encode clues:

    # 1. The root beer lover is the person who owns a Honda Civic.
    add_eq("root beer", "honda civic")

    # 2. The person who likes milk is directly left of the person who loves eating grilled cheese.
    next_left_pairs.append(("milk", "grilled cheese"))

    # 3. Alice is the person who uses a Samsung Galaxy S21.
    add_eq("Alice", "samsung galaxy s21")

    # 4. Alice is the person who loves stir fry.
    add_eq("Alice", "stir fry")

    # 5. The tea drinker is not in the fifth house.
    not_pos.append(("tea", 4))

    # 6. The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
    left_of_pairs.append(("bmw 3 series", "tea"))

    # 7. The person who is a doctor is Arnold.
    add_eq("doctor", "Arnold")

    # 8. The person who uses an iPhone 13 is the coffee drinker.
    add_eq("iphone 13", "coffee")

    # 9. The person who is an engineer is the person who owns a BMW 3 Series.
    add_eq("engineer", "bmw 3 series")

    # 10. The person who loves the stew is the person who uses an iPhone 13.
    add_eq("stew", "iphone 13")

    # 11. The person who is a doctor is directly left of the person who uses a OnePlus 9.
    next_left_pairs.append(("doctor", "oneplus 9"))

    # 12. The person who owns a Honda Civic is directly left of the person who loves the spaghetti eater. (interpreted as: left of the spaghetti eater)
    next_left_pairs.append(("honda civic", "spaghetti"))

    # 13. The person who uses a Google Pixel 6 is the tea drinker.
    add_eq("google pixel 6", "tea")

    # 14. Alice is the person who is an artist.
    add_eq("Alice", "artist")

    # 15. There is one house between Alice and the person who owns a Ford F-150.
    dist_pairs.append(("Alice", "ford f150", 2))

    # 16. Arnold is the person who owns a Toyota Camry.
    add_eq("Arnold", "toyota camry")

    # 17. Eric is in the fourth house. (0-indexed -> 3)
    abs_pos.append(("Eric", 3))

    # 18. The person who uses a OnePlus 9 is the person who is a lawyer.
    add_eq("oneplus 9", "lawyer")

    # 19. The person who loves eating grilled cheese is Peter.
    add_eq("grilled cheese", "Peter")

    # Positions mapping: value -> house index (0..4), or None if unassigned
    positions: Dict[str, Optional[int]] = {v: None for v in all_values}
    # Used houses per category
    used_houses_by_cat: Dict[str, Set[int]] = {cat: set() for cat in categories.keys()}

    # Pre-assign absolute positions
    for val, pos in abs_pos:
        positions[val] = pos
        used_houses_by_cat[value_to_category[val]].add(pos)

    # Helper: check if assignment is consistent
    def constraints_ok() -> bool:
        # Equality constraints
        for a, b in eq_pairs:
            pa, pb = positions[a], positions[b]
            if pa is not None and pb is not None and pa != pb:
                return False

        # Not position constraints
        for v, p in not_pos:
            pv = positions[v]
            if pv is not None and pv == p:
                return False

        # Absolute positions already set above mismatches are impossible via used houses violation

        # Next-left constraints
        for l, r in next_left_pairs:
            pl, pr = positions[l], positions[r]
            if pl is not None and pr is not None:
                if pl != pr - 1:
                    return False
            if pl is not None and (pl < 0 or pl > 3):
                # left item cannot be at last house if immediate-left (0..3 only)
                return False
            if pr is not None and (pr < 1 or pr > 4):
                # right item cannot be at first house
                return False

        # Left-of constraints
        for l, r in left_of_pairs:
            pl, pr = positions[l], positions[r]
            if pl is not None and pr is not None:
                if not (pl < pr):
                    return False
            if pl is not None and pl == 4:
                # cannot be at the last house if must be to the left of someone
                return False
            if pr is not None and pr == 0:
                # cannot be at the first house if someone must be to the left of you
                return False

        # Distance constraints
        for a, b, d in dist_pairs:
            pa, pb = positions[a], positions[b]
            if pa is not None and pb is not None:
                if abs(pa - pb) != d:
                    return False

        # Category uniqueness: within each category, no duplicate house
        for cat, used in used_houses_by_cat.items():
            if len(used) != len(set(used)):
                return False

        return True

    # Compute domain for a value considering current assignments and basic constraint-based pruning
    def domain_for(value: str) -> List[int]:
        if positions[value] is not None:
            return [positions[value]]

        cat = value_to_category[value]
        used = used_houses_by_cat[cat]
        domain = set(range(5)) - used

        # Not position constraints
        for v, p in not_pos:
            if v == value and p in domain:
                domain.discard(p)

        # Absolute position (if any)
        for v, p in abs_pos:
            if v == value:
                domain = {p}

        # Equality pairs
        for a, b in eq_pairs:
            if a == value:
                pb = positions[b]
                if pb is not None:
                    domain = {pb}
            elif b == value:
                pa = positions[a]
                if pa is not None:
                    domain = {pa}

        # Next-left constraints
        for l, r in next_left_pairs:
            if l == value:
                # l must be 0..3; and if r assigned, l = r-1
                pr = positions[r]
                if pr is not None:
                    domain = domain & {pr - 1}
                else:
                    domain = {h for h in domain if 0 <= h <= 3}
            elif r == value:
                pl = positions[l]
                if pl is not None:
                    domain = domain & {pl + 1}
                else:
                    domain = {h for h in domain if 1 <= h <= 4}

        # Left-of constraints
        for l, r in left_of_pairs:
            if l == value:
                pr = positions[r]
                if pr is not None:
                    domain = {h for h in domain if h < pr}
                else:
                    domain = {h for h in domain if h <= 3}  # cannot be 4
            elif r == value:
                pl = positions[l]
                if pl is not None:
                    domain = {h for h in domain if h > pl}
                else:
                    domain = {h for h in domain if h >= 1}  # cannot be 0

        # Distance constraints
        for a, b, d in dist_pairs:
            if a == value:
                pb = positions[b]
                if pb is not None:
                    domain = domain & {pb - d, pb + d}
                else:
                    # any h that has partner within 0..4
                    domain = {h for h in domain if 0 <= h - d <= 4 or 0 <= h + d <= 4}
            elif b == value:
                pa = positions[a]
                if pa is not None:
                    domain = domain & {pa - d, pa + d}
                else:
                    domain = {h for h in domain if 0 <= h - d <= 4 or 0 <= h + d <= 4}

        # Keep only valid house indices
        domain = {h for h in domain if 0 <= h <= 4}

        return sorted(domain)

    # Choose next unassigned value with smallest domain (MRV heuristic)
    def select_unassigned() -> Optional[str]:
        best_v = None
        best_size = None
        for v in all_values:
            if positions[v] is None:
                dom = domain_for(v)
                size = len(dom)
                if size == 0:
                    return v  # immediate failure candidate
                if best_size is None or size < best_size:
                    best_size = size
                    best_v = v
                    if size == 1:
                        break
        return best_v

    solved = False

    def backtrack():
        nonlocal solved
        if solved:
            return
        # If all assigned, success
        if all(positions[v] is not None for v in all_values):
            if constraints_ok():
                solved = True
            return

        var = select_unassigned()
        if var is None:
            return

        dom = domain_for(var)
        # If domain empty, dead end
        if not dom:
            return

        cat = value_to_category[var]
        for h in dom:
            # Assign
            positions[var] = h
            used_houses_by_cat[cat].add(h)

            if constraints_ok():
                backtrack()
                if solved:
                    return

            # Undo
            positions[var] = None
            used_houses_by_cat[cat].discard(h)

    backtrack()

    if not solved:
        raise RuntimeError("No solution found for the given puzzle constraints.")

    # Build rows per house
    header = ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"]
    rows = []
    # Precompute inverse maps: for each category and house, find the value
    house_to_value: Dict[str, List[str]] = {}
    for cat, vals in categories.items():
        inv = [""] * 5
        for v in vals:
            inv[positions[v]] = v
        house_to_value[cat] = inv

    for i in range(5):
        row = [
            str(i + 1),
            house_to_value["Name"][i],
            house_to_value["Food"][i],
            house_to_value["CarModel"][i],
            house_to_value["PhoneModel"][i],
            house_to_value["Occupation"][i],
            house_to_value["Drink"][i],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))