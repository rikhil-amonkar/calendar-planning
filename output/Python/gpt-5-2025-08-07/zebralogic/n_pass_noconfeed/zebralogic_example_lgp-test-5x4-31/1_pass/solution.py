import json
from itertools import permutations

def solve_puzzle():
    # Houses are indexed 0..4 corresponding to 1..5
    houses = [0, 1, 2, 3, 4]

    Names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    Vacations = ["cruise", "city", "camping", "beach", "mountain"]
    Children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    Nationalities = ["dane", "norwegian", "brit", "german", "swede"]

    # Constraints summary encoded:
    # 1. Norwegian is Peter -> nationality at Peter's house is norwegian
    # 2. Swede's child is Bella
    # 3. Beach is directly left of Samantha
    # 4. Bella not in house 2 (index 1)
    # 5. Alice is British
    # 6. Cruises in house 1 (index 0)
    # 7. Meredith in house 4 (index 3)
    # 8. Eric not in house 5 (index 4). Redundant since we'll fix house 5 name = Arnold
    # 9. Swede right of Norwegian
    # 10. One house between Fred and City (abs diff = 2)
    # 11. Bob enjoys camping
    # 12. Dane is in house 5 (index 4)
    # 13. Camping not in house 5 (implies Bob not in house 5)

    solutions = []

    # Name assignments: fix house 5 (index 4) = Arnold, and Bob cannot be in house 1 due to cruise vs camping
    remaining_names = ["Alice", "Bob", "Eric", "Peter"]
    for perm_names in permutations(remaining_names):
        names = list(perm_names) + ["Arnold"]
        # Bob not in house 1 (index 0) because house 1 is cruise and Bob is camping
        if names[0] == "Bob":
            continue
        # Eric not in house 5 is automatically satisfied since house 5 is Arnold

        idx_name = {name: i for i, name in enumerate(names)}

        # Nationalities: fix house 5 = dane, house3 (index2) = swede (deduced from constraints),
        #               Peter's house = norwegian, Alice's house = brit
        nat = [None] * 5
        nat[4] = "dane"
        nat[2] = "swede"

        # Peter must be Norwegian and to the left of Swede (index 2), so Peter must be in index 0 or 1
        idx_peter = idx_name["Peter"]
        if idx_peter not in (0, 1):
            continue
        nat[idx_peter] = "norwegian"

        # Alice is British
        idx_alice = idx_name["Alice"]
        if nat[idx_alice] is not None and nat[idx_alice] != "brit":
            continue
        nat[idx_alice] = "brit"

        # Check uniqueness so far and fill remaining nationality as german
        used_nats = set(x for x in nat if x is not None)
        if len(used_nats) != len([x for x in nat if x is not None]):
            # Duplicated assignment
            continue

        # Remaining nationality is german for the remaining house
        remaining_nat_values = set(Nationalities) - set(nat)
        if len(remaining_nat_values) != 1:
            continue
        remaining_nat = remaining_nat_values.pop()
        # Find the index where nat is None
        try:
            remaining_idx = nat.index(None)
        except ValueError:
            # All filled; should not happen here
            remaining_idx = None
        if remaining_idx is None:
            continue
        nat[remaining_idx] = remaining_nat

        # Validate Swede right of Norwegian
        if not (2 > idx_peter):  # swede at index 2 must be right of Norwegian
            continue

        # Children: fix house 4 (index3) = Meredith, swede's child Bella at index 2, and Bella not in house 2 (index1)
        # Remaining children at indices [0,1,4]: Samantha, Fred, Timothy with Samantha not at index 0 (no left house for beach)
        children = [None] * 5
        children[3] = "Meredith"
        # Swede at index 2: their child is Bella
        children[2] = "Bella"
        # Bella not in house 2 (index 1) satisfied as above

        remaining_children_positions = [0, 1, 4]
        remaining_children_values = ["Samantha", "Fred", "Timothy"]

        # Samantha cannot be in house 1 (index 0) due to left-of beach constraint
        for perm_child_vals in permutations(remaining_children_values):
            if perm_child_vals[0] == "Samantha":
                continue
            for pos, val in zip(remaining_children_positions, perm_child_vals):
                children[pos] = val

            # Vacations: fix house 1 (index0) = cruise, Bob's house = camping, camping not in house 5 ensured by Bob not at 5
            vacations = [None] * 5
            vacations[0] = "cruise"
            idx_bob = idx_name["Bob"]
            # Bob cannot be in index 0 (already filtered), set his vacation
            vacations[idx_bob] = "camping"
            if idx_bob == 4:
                # Camping not in house 5
                continue

            # Assign remaining vacations to remaining indices
            remaining_vac_positions = [i for i in houses if vacations[i] is None]
            remaining_vac_values = [v for v in Vacations if v not in vacations]

            for perm_vac_vals in permutations(remaining_vac_values):
                vac_try = vacations[:]
                for pos, val in zip(remaining_vac_positions, perm_vac_vals):
                    vac_try[pos] = val

                # Constraint 3: Beach is directly left of Samantha
                idx_sam = children.index("Samantha")
                if idx_sam == 0:
                    continue
                if not (vac_try[idx_sam - 1] == "beach"):
                    continue

                # Constraint 10: One house between Fred and City
                idx_fred = children.index("Fred")
                idx_city = vac_try.index("city")
                if abs(idx_fred - idx_city) != 2:
                    continue

                # All constraints satisfied, record solution
                solutions.append((names, vac_try, children, nat))

    if not solutions:
        raise ValueError("No solution found")

    # If multiple solutions, take the first (should be unique for this puzzle)
    names, vacations, children, nat = solutions[0]

    # Build JSON output structure
    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": []
        }
    }

    for i in range(5):
        row = [
            str(i + 1),
            names[i],
            vacations[i],
            children[i],
            nat[i]
        ]
        output["solution"]["rows"].append(row)

    return output


if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))