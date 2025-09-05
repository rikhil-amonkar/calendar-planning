import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]

    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]

    # Indexing houses as 0..5 for internal calculations
    H1, H2, H3, H4, H5, H6 = 0, 1, 2, 3, 4, 5

    solutions = []

    # Pre-assignments from clues:
    # 2. The person who uses a Huawei P50 is in the first house. -> phone[H1] = "huawei p50"
    # 7. The person who uses a Huawei P50 is Eric. -> name[H1] = "Eric"
    # 3. The person who uses a OnePlus 9 is in the sixth house. -> phone[H6] = "oneplus 9"
    # 10. Arnold is the person who uses a OnePlus 9. -> name[H6] = "Arnold"
    # 8. The person who uses a Xiaomi Mi 11 is in the third house. -> phone[H3] = "xiaomi mi 11"
    fixed_names = [None] * 6
    fixed_names[H1] = "Eric"
    fixed_names[H6] = "Arnold"

    fixed_phones = [None] * 6
    fixed_phones[H1] = "huawei p50"
    fixed_phones[H3] = "xiaomi mi 11"
    fixed_phones[H6] = "oneplus 9"

    # Remaining names to place in houses 2..5
    remaining_names = [n for n in names if n not in fixed_names]
    houses_to_fill_for_names = [i for i in range(6) if fixed_names[i] is None]  # [1,2,3,4]
    for perm in itertools.permutations(remaining_names):
        name_at = fixed_names[:]
        for idx, h in enumerate(houses_to_fill_for_names):
            name_at[h] = perm[idx]

        # Apply name-based constraints:
        # 6. There is one house between Bob and Carol. -> |pos(Bob) - pos(Carol)| == 2
        pos = {name_at[i]: i for i in range(6)}
        if abs(pos["Bob"] - pos["Carol"]) != 2:
            continue
        # 9. Alice is somewhere to the left of Carol.
        if not (pos["Alice"] < pos["Carol"]):
            continue

        # Now assign phones with constraints

        # Prepare phone assignment array with fixed phones
        phone_at = fixed_phones[:]

        # 1. The person who uses an iPhone 13 is Alice. -> house_of(Alice) has phone "iphone 13"
        alice_house = pos["Alice"]
        # 5. The person who uses an iPhone 13 is not in the second house. -> alice_house != H2
        if alice_house == H2:
            continue
        if phone_at[alice_house] is not None and phone_at[alice_house] != "iphone 13":
            # Contradiction with fixed phones (should not happen here but keep safe)
            continue
        phone_at[alice_house] = "iphone 13"

        # Remaining phones to assign to remaining houses
        assigned_phones = {p for p in phone_at if p is not None}
        remaining_phones = [p for p in phones if p not in assigned_phones]
        houses_to_fill_for_phones = [i for i in range(6) if phone_at[i] is None]

        # Additional phone constraints:
        # 4. The person who uses a Google Pixel 6 is not in the second house. -> phone_at[H2] != "google pixel 6"
        # 5. iPhone already enforced with Alice.
        # 7 and 10 already consistent with fixed name-phone-house assignments.

        # We can prune: if H2 is in houses_to_fill_for_phones, remove "google pixel 6" from candidates when placing there
        for perm_phones in itertools.permutations(remaining_phones):
            valid = True
            tentative_phone_at = phone_at[:]
            for idx, h in enumerate(houses_to_fill_for_phones):
                p = perm_phones[idx]
                # Enforce constraint for H2
                if h == H2 and p in ("iphone 13", "google pixel 6"):
                    valid = False
                    break
                tentative_phone_at[h] = p

            if not valid:
                continue

            # Cross-check name-phone identity constraints:
            # 1. Alice uses iPhone 13 -> already enforced
            # 7. Huawei P50 is Eric -> enforced by fixed placements
            # 10. OnePlus 9 is Arnold -> enforced by fixed placements

            # All constraints satisfied; collect solution
            solutions.append((name_at, tentative_phone_at))

    # Expect a unique solution
    if not solutions:
        raise ValueError("No solution found.")
    # If multiple, pick the first deterministic one
    name_at, phone_at = solutions[0]

    # Prepare JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "PhoneModel"],
            "rows": []
        }
    }
    for i in range(6):
        output["solution"]["rows"].append([str(i + 1), name_at[i], phone_at[i]])

    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))