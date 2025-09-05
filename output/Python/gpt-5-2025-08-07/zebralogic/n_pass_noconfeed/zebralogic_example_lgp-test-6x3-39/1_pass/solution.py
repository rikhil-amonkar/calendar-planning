import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

    # Variables are tuples: (category, value)
    name_vars = [("name", n) for n in names]
    child_vars = [("child", c) for c in children]
    smoothie_vars = [("smoothie", s) for s in smoothies]
    variables = name_vars + child_vars + smoothie_vars

    # For uniqueness within each category, track used houses
    used = {
        "name": set(),
        "child": set(),
        "smoothie": set(),
    }

    # Base domain restrictions
    base_restrictions = {}
    for var in variables:
        base_restrictions[var] = set(houses)

    # Apply initial domain restrictions from clues
    # 3. Alice is not in the fifth house. (Name Alice)
    base_restrictions[("name", "Alice")].discard(5)
    # 4. The person's child is named Samantha is not in the second house.
    base_restrictions[("child", "Samantha")].discard(2)
    # 9. Arnold is not in the second house.
    base_restrictions[("name", "Arnold")].discard(2)
    # 13. The person's child is named Meredith is in the sixth house.
    base_restrictions[("child", "Meredith")] = {6}
    # 14. The Dragonfruit smoothie lover is the person's child is named Meredith. => dragonfruit at same house as Meredith's mom (who is in 6)
    base_restrictions[("smoothie", "dragonfruit")] = {6}
    # From left-of constraints that are impossible at edges (optional early pruning):
    # 12. Cherry immediately left of Samantha's mom -> cherry cannot be in 6
    base_restrictions[("smoothie", "cherry")].discard(6)

    # Helper to get assigned value
    def get(assign, var):
        return assign.get(var)

    # Constraint checker
    def consistent(assign):
        # Unpack helper: find house of an entity given category and value
        def H(cat, val):
            return get(assign, (cat, val))

        # 11. Arnold is directly left of Carol.
        a = H("name", "Arnold")
        c = H("name", "Carol")
        if a is not None and c is not None:
            if a + 1 != c:
                return False
        else:
            # Partial feasibility
            if a is not None and (a == 6):  # cannot have Carol at 7
                return False
            if c is not None and (c == 1):  # cannot have Arnold at 0
                return False
        # 9. Arnold is not in the second house.
        if a is not None and a == 2:
            return False

        # 3. Alice is not in the fifth house.
        al = H("name", "Alice")
        if al is not None and al == 5:
            return False

        # 6. Alice is the person's child is named Alice. (same house)
        child_al = H("child", "Alice")
        if al is not None and child_al is not None and al != child_al:
            return False
        # Partial feasibility: if one assigned, ensure other can be same house within category uniqueness
        # (handled naturally by search; no extra check needed)

        # 10. Bob is the person who is the mother of Timothy. (same house)
        bob = H("name", "Bob")
        tim = H("child", "Timothy")
        if bob is not None and tim is not None and bob != tim:
            return False

        # 13. Meredith's mom in 6
        mer = H("child", "Meredith")
        if mer is not None and mer != 6:
            return False

        # 14. Dragonfruit smoothie lover is the person's child is named Meredith (same house)
        drag = H("smoothie", "dragonfruit")
        if drag is not None and mer is not None and drag != mer:
            return False

        # 7. Alice is the Watermelon smoothie lover. (same house)
        wal = H("smoothie", "watermelon")
        if al is not None and wal is not None and al != wal:
            return False

        # 12. Cherry immediately left of Samantha's mom: cherry + 1 == sam
        ch = H("smoothie", "cherry")
        sam = H("child", "Samantha")
        if ch is not None and sam is not None:
            if ch + 1 != sam:
                return False
        else:
            # Partial feasibility
            if ch is not None and ch == 6:
                return False
            if sam is not None and sam == 1:
                return False

        # 4. Samantha's mom not in 2.
        if sam is not None and sam == 2:
            return False

        # 5. Watermelon is somewhere to the right of Cherry.
        if wal is not None and ch is not None:
            if not (wal > ch):
                return False
        else:
            if wal is not None and wal == 1:
                # cannot be right of any
                return False
            if ch is not None and ch == 6:
                return False

        # 8. Peter is somewhere to the right of Samantha's mom.
        pet = H("name", "Peter")
        if pet is not None and sam is not None:
            if not (pet > sam):
                return False
        else:
            if pet is not None and pet == 1:
                return False
            if sam is not None and sam == 6:
                return False

        # 1. The person's child is named Fred and the Desert smoothie lover are next to each other.
        fr = H("child", "Fred")
        des = H("smoothie", "desert")
        if fr is not None and des is not None:
            if abs(fr - des) != 1:
                return False
        # no strong partial pruning here

        # 2. Blueberry is somewhere to the left of the person's child is named Fred.
        bb = H("smoothie", "blueberry")
        if bb is not None and fr is not None:
            if not (bb < fr):
                return False
        else:
            if bb is not None and bb == 6:
                return False
            if fr is not None and fr == 1:
                return False

        # 5 also implies via 7 that Alice (watermelon) must be to the right of cherry, which is checked above.

        return True

    # Compute domain for a variable considering used houses and base restrictions
    def domain_for(var, assign, used):
        cat, val = var
        domain = set(base_restrictions[var])
        # Enforce uniqueness within category
        domain -= used[cat]
        # Additional quick prunes from constraints that are single-variable:
        # Already handled via base_restrictions. Others we will let consistent() handle.
        return sorted(domain)

    # Select unassigned variable with MRV
    def select_unassigned_var(assign, used):
        unassigned = [v for v in variables if v not in assign]
        # Order by domain size (MRV), then by category to stabilize
        scored = []
        for v in unassigned:
            dom = domain_for(v, assign, used)
            scored.append((len(dom), 0 if v[0]=="child" else 1 if v[0]=="smoothie" else 2, v, dom))
        scored.sort(key=lambda x: (x[0], x[1]))  # smallest domain first
        if not scored:
            return None, []
        return scored[0][2], scored[0][3]

    def backtrack(assign, used):
        if len(assign) == len(variables):
            if consistent(assign):
                return assign
            return None

        var, dom = select_unassigned_var(assign, used)
        if var is None:
            return None

        cat, val = var
        for h in dom:
            # Assign and check consistency
            assign[var] = h
            used[cat].add(h)
            if consistent(assign):
                res = backtrack(assign, used)
                if res is not None:
                    return res
            # Undo
            used[cat].remove(h)
            del assign[var]
        return None

    solution_assign = backtrack({}, {k: set(v) for k, v in used.items()})
    if solution_assign is None:
        raise RuntimeError("No solution found")

    # Build final table by house
    # For each house 1..6, find the name, child, smoothie assigned to that house
    rows = []
    for h in houses:
        # find name at house h
        name_at = next(n for n in names if solution_assign[("name", n)] == h)
        child_at = next(c for c in children if solution_assign[("child", c)] == h)
        smoothie_at = next(s for s in smoothies if solution_assign[("smoothie", s)] == h)
        rows.append([str(h), name_at, child_at, smoothie_at])

    output = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()