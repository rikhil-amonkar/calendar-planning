import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]

    # Constraints as data
    fixed_phone_positions = {
        1: "huawei p50",          # Clue 2
        3: "xiaomi mi 11",         # Clue 8
        6: "oneplus 9"             # Clue 3
    }
    not_in_positions = {
        "google pixel 6": {2},     # Clue 4
        "iphone 13": {2}           # Clue 5
    }
    # Name-phone bindings
    phone_to_name = {
        "iphone 13": "Alice",      # Clue 1
        "huawei p50": "Eric",      # Clue 7
        "oneplus 9": "Arnold"      # Clue 10
    }

    solutions = []

    # Pre-assign names based on phone/name bindings from fixed phone positions
    # From Clues 2 and 7: House 1 -> Huawei P50 -> Eric
    # From Clues 3 and 10: House 6 -> OnePlus 9 -> Arnold
    fixed_name_positions = {
        1: "Eric",
        6: "Arnold"
    }

    remaining_names = [n for n in names if n not in fixed_name_positions.values()]
    # Positions 2,3,4,5 are to be filled
    for perm in permutations(remaining_names, 4):
        name_by_pos = {
            1: fixed_name_positions[1],
            6: fixed_name_positions[6],
            2: perm[0],
            3: perm[1],
            4: perm[2],
            5: perm[3]
        }

        # Apply name-based constraints
        # Clue 6: There is one house between Bob and Carol (distance 2)
        pos_bob = next(p for p, n in name_by_pos.items() if n == "Bob")
        pos_carol = next(p for p, n in name_by_pos.items() if n == "Carol")
        if abs(pos_bob - pos_carol) != 2:
            continue

        # Clue 9: Alice is somewhere to the left of Carol
        pos_alice = next(p for p, n in name_by_pos.items() if n == "Alice")
        if not (pos_alice < pos_carol):
            continue

        # Phone assignment
        phone_by_pos = dict(fixed_phone_positions)

        # Ensure name-phone bindings for fixed phones are respected
        # Clue 7: House 1 (Huawei) -> Eric; already ensured by fixed_name_positions
        if name_by_pos[1] != phone_to_name[phone_by_pos[1]]:
            continue
        # Clue 10: House 6 (OnePlus) -> Arnold
        if name_by_pos[6] != phone_to_name[phone_by_pos[6]]:
            continue

        # Remaining phones to assign
        assigned_phones = set(phone_by_pos.values())
        remaining_phones = [p for p in phones if p not in assigned_phones]

        # Positions left to assign: 2,4,5
        # Apply "not in positions" constraints for pos 2
        pos2_allowed = [p for p in remaining_phones if 2 not in not_in_positions.get(p, set())]
        if len(pos2_allowed) == 1:
            phone_by_pos[2] = pos2_allowed[0]
            remaining_phones.remove(pos2_allowed[0])
        else:
            # If more than one allowed or none, skip (should be exactly one: "samsung galaxy s21")
            continue

        # For positions 4 and 5, respect iPhone 13 <-> Alice
        # Clue 1: The person who uses an iPhone 13 is Alice
        alice_phone = "iphone 13"
        if alice_phone not in remaining_phones:
            continue

        # Assign iPhone to Alice's position (must be either 4 or 5)
        if pos_alice in (4, 5):
            phone_by_pos[pos_alice] = alice_phone
            remaining_phones.remove(alice_phone)
        else:
            # If Alice is not in 4 or 5, impossible due to earlier deductions
            continue

        # Assign the last remaining phone to the other position among 4 and 5
        other_pos = 4 if pos_alice == 5 else 5
        if len(remaining_phones) != 1:
            continue
        phone_by_pos[other_pos] = remaining_phones[0]

        # Validate remaining constraints: not_in_positions for all
        valid = True
        for p, ph in phone_by_pos.items():
            if p in not_in_positions.get(ph, set()):
                valid = False
                break
        if not valid:
            continue

        # Double-check all name-phone bindings
        # iphone 13 -> Alice
        if name_by_pos[next(pos for pos, ph in phone_by_pos.items() if ph == "iphone 13")] != "Alice":
            continue
        # huawei p50 -> Eric
        if name_by_pos[next(pos for pos, ph in phone_by_pos.items() if ph == "huawei p50")] != "Eric":
            continue
        # oneplus 9 -> Arnold
        if name_by_pos[next(pos for pos, ph in phone_by_pos.items() if ph == "oneplus 9")] != "Arnold":
            continue

        # All constraints satisfied
        solutions.append((name_by_pos, phone_by_pos))

    # Expect a unique solution
    if len(solutions) != 1:
        raise ValueError(f"Expected a unique solution, found {len(solutions)}.")

    name_by_pos, phone_by_pos = solutions[0]

    # Prepare JSON output
    result = {
        "solution": {
            "header": ["House", "Name", "PhoneModel"],
            "rows": []
        }
    }
    for house in houses:
        result["solution"]["rows"].append([
            str(house),
            name_by_pos[house],
            phone_by_pos[house]
        ])
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))