import json
from itertools import product

def solve():
    houses = list(range(5))  # 0..4

    Names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    Vacations = ["cruise", "city", "camping", "beach", "mountain"]
    Children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    Nationals = ["dane", "norwegian", "brit", "german", "swede"]

    # Indices for quick reference
    idx_name = {n: i for i, n in enumerate(Names)}
    idx_vac = {v: i for i, v in enumerate(Vacations)}
    idx_child = {c: i for i, c in enumerate(Children)}
    idx_nat = {n: i for i, n in enumerate(Nationals)}

    # Assignment arrays, None means unassigned
    name = [None] * 5
    vac = [None] * 5
    child = [None] * 5
    nat = [None] * 5

    # Remaining pools
    names_left = set(Names)
    vac_left = set(Vacations)
    child_left = set(Children)
    nat_left = set(Nationals)

    # Apply fixed constraints from the start
    # C6: cruise is in the first house.
    vac[0] = "cruise"
    vac_left.remove("cruise")

    # C7: Meredith is in the fourth house (index 3).
    child[3] = "Meredith"
    child_left.remove("Meredith")

    # C12: The Dane is in the fifth house (index 4).
    nat[4] = "dane"
    nat_left.remove("dane")

    # Helper functions for checks
    def equal_link_ok(nm, vc, ch, na):
        # C1: Peter <-> Norwegian
        if nm == "Peter" and na is not None and na != "norwegian":
            return False
        if na == "norwegian" and nm is not None and nm != "Peter":
            return False
        # C5: Alice <-> Brit
        if nm == "Alice" and na is not None and na != "brit":
            return False
        if na == "brit" and nm is not None and nm != "Alice":
            return False
        # C11: Bob <-> Camping
        if nm == "Bob" and vc is not None and vc != "camping":
            return False
        if vc == "camping" and nm is not None and nm != "Bob":
            return False
        # C2: Swede <-> Bella
        if na == "swede" and ch is not None and ch != "Bella":
            return False
        if ch == "Bella" and na is not None and na != "swede":
            return False
        return True

    def can_place_city_at(pos):
        if not (0 <= pos < 5):
            return False
        if vac[pos] is not None:
            return vac[pos] == "city"
        # If unassigned, city must still be available and not forbidden by fixed rule (house 0 is cruise)
        if pos == 0:
            return False  # house 1 already cruise
        return "city" in vac_left

    def can_place_fred_at(pos):
        if not (0 <= pos < 5):
            return False
        if child[pos] is not None:
            return child[pos] == "Fred"
        # House 4 (index 3) must be Meredith
        if pos == 3:
            return False
        return "Fred" in child_left

    def can_place_samantha_at(pos):
        if not (0 <= pos < 5):
            return False
        if child[pos] is not None:
            return child[pos] == "Samantha"
        # If unassigned, ensure Samantha still available and not blocked by fixed child at house 4
        if pos == 3:
            return False
        return "Samantha" in child_left

    def can_place_beach_at(pos):
        if not (0 <= pos < 5):
            return False
        if vac[pos] is not None:
            return vac[pos] == "beach"
        # Beach cannot be at last house (needs right neighbor)
        if pos == 4:
            return False
        return "beach" in vac_left

    def check_partial():
        # C4: Bella is not in the second house (index 1)
        if child[1] == "Bella":
            return False
        # C8: Eric is not in the fifth house (index 4)
        if name[4] == "Eric":
            return False
        # C13: Camping is not in the fifth house
        if vac[4] == "camping":
            return False
        # C6, C7, C12 already enforced at initialization

        # Equality links for all assigned houses
        for i in range(5):
            if any(x is not None for x in (name[i], vac[i], child[i], nat[i])):
                if not equal_link_ok(name[i], vac[i], child[i], nat[i]):
                    return False

        # C3: Beach directly left of Samantha
        for i in range(5):
            if vac[i] == "beach":
                if i == 4:
                    return False
                # right neighbor must be Samantha
                if child[i + 1] is not None and child[i + 1] != "Samantha":
                    return False
                if child[i + 1] is None:
                    if not can_place_samantha_at(i + 1):
                        return False
            if child[i] == "Samantha":
                if i == 0:
                    return False
                # left neighbor must be beach
                if vac[i - 1] is not None and vac[i - 1] != "beach":
                    return False
                if vac[i - 1] is None:
                    if not can_place_beach_at(i - 1):
                        return False

        # C10: One house between Fred and City
        fred_idx = next((i for i in range(5) if child[i] == "Fred"), None)
        city_idx = next((i for i in range(5) if vac[i] == "city"), None)
        if fred_idx is not None and city_idx is not None:
            if abs(fred_idx - city_idx) != 2:
                return False
        elif fred_idx is not None and city_idx is None:
            ok = False
            for t in [fred_idx - 2, fred_idx + 2]:
                if can_place_city_at(t):
                    ok = True
                    break
            if not ok:
                return False
        elif city_idx is not None and fred_idx is None:
            ok = False
            for t in [city_idx - 2, city_idx + 2]:
                if can_place_fred_at(t):
                    ok = True
                    break
            if not ok:
                return False

        # C9: Swede is somewhere to the right of the Norwegian (Peter)
        # Find possible positions for Norwegian and Swede given partial info
        nor_idx_assigned = next((i for i in range(5) if nat[i] == "norwegian"), None)
        swe_idx_assigned = next((i for i in range(5) if nat[i] == "swede"), None)

        # If both assigned, check order
        if nor_idx_assigned is not None and swe_idx_assigned is not None:
            if not (swe_idx_assigned > nor_idx_assigned):
                return False
        else:
            # Compute potential indices for each based on current partial info
            possible_nor = set()
            possible_swe = set()
            for i in range(5):
                # Danish house is fixed at 4
                if i == 4:
                    continue
                # Possible Norwegian (must be Peter)
                if nat[i] is None:
                    # Nationality Norwegian must be available
                    if "norwegian" in nat_left:
                        # Name must be Peter at that house when assigned; if name assigned, must be Peter
                        if name[i] is None or name[i] == "Peter":
                            possible_nor.add(i)
                elif nat[i] == "norwegian":
                    possible_nor.add(i)

                # Possible Swede (must have Bella as child)
                if nat[i] is None:
                    if "swede" in nat_left:
                        # Child must be Bella at that house; if child assigned, must be Bella
                        if child[i] is None or child[i] == "Bella":
                            # Also Bella not allowed at house 1 (index 1) per C4
                            if not (i == 1 and (child[i] is None)):  # If unassigned, Bella cannot be later assigned to index 1
                                possible_swe.add(i)
                            else:
                                # If i==1 and child[i] already assigned Bella (which is illegal), would have failed earlier in C4
                                pass
                elif nat[i] == "swede":
                    possible_swe.add(i)

            # Enforce right-of relation on possible sets
            if nor_idx_assigned is not None:
                # Swede must be strictly to the right of fixed Norwegian
                if not any(j > nor_idx_assigned for j in possible_swe):
                    return False
            elif swe_idx_assigned is not None:
                # Norwegian must be strictly to the left of fixed Swede
                if not any(i < swe_idx_assigned for i in possible_nor):
                    return False
            else:
                # Both unassigned: there must exist at least one pair i<j with i in possible_nor and j in possible_swe
                if possible_nor and possible_swe:
                    if not any(i < j for i in possible_nor for j in possible_swe):
                        return False
                else:
                    # One of them has no possible positions left
                    return False

        return True

    solution = []

    def backtrack(h):
        # If all houses assigned, validate and record solution
        if h == 5:
            if check_partial():
                solution.append({
                    "name": list(name),
                    "vac": list(vac),
                    "child": list(child),
                    "nat": list(nat),
                })
            return

        # Prepare allowed sets for this house considering fixed constraints
        allowed_names = set(names_left)
        allowed_vacs = set(vac_left)
        allowed_child = set(child_left)
        allowed_nat = set(nat_left)

        # House-specific fixed constraints
        if h == 0:
            # Already set vac[0] = "cruise"
            allowed_vacs = {"cruise"} if vac[0] == "cruise" else set()
        else:
            # Ensure cruise not allowed elsewhere
            if "cruise" in allowed_vacs:
                allowed_vacs.remove("cruise")

        if h == 3:
            # Meredith fixed
            allowed_child = {"Meredith"} if child[3] == "Meredith" else set()
        else:
            if "Meredith" in allowed_child:
                allowed_child.remove("Meredith")

        if h == 1:
            # Bella not in second house
            if "Bella" in allowed_child:
                allowed_child.remove("Bella")

        if h == 4:
            # Dane fixed
            allowed_nat = {"dane"} if nat[4] == "dane" else set()
            # Eric not in fifth house
            if "Eric" in allowed_names:
                allowed_names.remove("Eric")
            # Camping not in fifth house
            if "camping" in allowed_vacs:
                allowed_vacs.remove("camping")
        else:
            # Not house 5: nationality cannot be dane if unassigned
            if "dane" in allowed_nat:
                allowed_nat.remove("dane")

        # Iterate over possible combinations for this house
        for nm in sorted(allowed_names):
            for vc in sorted(allowed_vacs):
                for ch in sorted(allowed_child):
                    for na in sorted(allowed_nat):
                        # Check equality links between attributes
                        if not equal_link_ok(nm, vc, ch, na):
                            continue

                        # Temporary assign
                        prev = (name[h], vac[h], child[h], nat[h])
                        name[h], vac[h], child[h], nat[h] = nm, vc, ch, na

                        # Remove from pools
                        names_left.remove(nm)
                        vac_left.discard(vc)
                        child_left.remove(ch)
                        nat_left.discard(na)

                        # Check partial constraints
                        if check_partial():
                            backtrack(h + 1)

                        # Undo assignment
                        names_left.add(nm)
                        if vc != "cruise" or h == 0:
                            vac_left.add(vc) if vc != "cruise" or h != 0 else vac_left.discard(vc)
                            # careful: vac[0] is fixed to cruise and removed at start; do not re-add
                        child_left.add(ch) if h != 3 else child_left.discard(ch)
                        # Do not re-add fixed nationality for house 5
                        if not (h == 4 and na == "dane"):
                            nat_left.add(na)

                        name[h], vac[h], child[h], nat[h] = prev

    # Start backtracking from house 0
    backtrack(0)

    if not solution:
        raise RuntimeError("No solution found")

    # Use the first solution
    sol = solution[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": []
        }
    }
    for i in range(5):
        row = [
            str(i + 1),
            sol["name"][i],
            sol["vac"][i],
            sol["child"][i],
            sol["nat"][i],
        ]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    solve()