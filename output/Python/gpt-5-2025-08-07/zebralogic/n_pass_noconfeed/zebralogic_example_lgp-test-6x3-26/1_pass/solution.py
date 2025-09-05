import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]

    Names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    Heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
    Phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    # Helper to check all clues
    def check_all_clues(name_pos, height_pos, phone_pos):
        # Convert maps (value -> house) for quick access
        # Clues:

        # 1. Bob is directly left of the person who is tall.
        if not (name_pos["Bob"] + 1 == height_pos["tall"]):
            return False

        # 2. Peter is somewhere to the left of the person who uses an iPhone 13.
        if not (name_pos["Peter"] < phone_pos["iphone 13"]):
            return False

        # 3. The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
        if not (height_pos["very short"] > phone_pos["google pixel 6"]):
            return False

        # 4. Carol is the person who is very tall.
        if not (name_pos["Carol"] == height_pos["very tall"]):
            return False

        # 5. There is one house between the person who uses a Google Pixel 6 and the person who is short.
        if not (abs(phone_pos["google pixel 6"] - height_pos["short"]) == 2):
            return False

        # 6. The person who uses a Samsung Galaxy S21 is not in the first house.
        if phone_pos["samsung galaxy s21"] == 1:
            return False

        # 7. The person who uses a OnePlus 9 is directly left of the person who is short.
        if not (phone_pos["oneplus 9"] + 1 == height_pos["short"]):
            return False

        # 8. The person who is tall is Arnold.
        if not (name_pos["Arnold"] == height_pos["tall"]):
            return False

        # 9. The person who is super tall is in the first house.
        if not (height_pos["super tall"] == 1):
            return False

        # 10. The person who uses a Xiaomi Mi 11 is Carol.
        if not (phone_pos["xiaomi mi 11"] == name_pos["Carol"]):
            return False

        # 11. The person who uses a Google Pixel 6 is somewhere to the right of Eric.
        if not (phone_pos["google pixel 6"] > name_pos["Eric"]):
            return False

        # 12. The person who is short is in the sixth house.
        if not (height_pos["short"] == 6):
            return False

        return True

    solution = None

    # Pre-deductions from constraints:
    # From (12): short = 6
    # From (7): oneplus9 directly left of short -> oneplus9 = 5
    # From (5): one house between gpixel6 and short -> gpixel6 = 4 (since short=6)
    # From (3) and (12): very short is right of gpixel6; with gpixel6=4 and short=6, very short must be 5.
    # From (9): super tall = 1
    # From (10) and (4): Carol is very tall and uses Xiaomi Mi 11.
    forced_heights = {1: "super tall", 5: "very short", 6: "short"}
    forced_phones = {4: "google pixel 6", 5: "oneplus 9"}

    # Enumerate name positions (permutations of names across houses)
    for name_perm in itertools.permutations(Names, 6):
        house_to_name = {h: name_perm[h - 1] for h in houses}
        name_pos = {house_to_name[h]: h for h in houses}

        # Apply name-only derived constraints
        # Bob directly left of Arnold (since Arnold is tall)
        if not (name_pos["Bob"] + 1 == name_pos["Arnold"]):
            continue

        # Eric must be to the left of gpixel6 at 4 -> Eric in {1,2,3}
        if not (name_pos["Eric"] < 4):
            continue

        # Carol is very tall; very tall cannot be in houses 1,5,6 (already set to other heights),
        # and house 4 has Google Pixel 6 (Carol uses Xiaomi), so Carol cannot be 4.
        # Hence Carol must be in {2,3}
        if name_pos["Carol"] not in (2, 3):
            continue

        # Arnold (tall) cannot be in 1,5,6; thus in {2,3,4}
        if name_pos["Arnold"] not in (2, 3, 4):
            continue

        # Prepare phones: start with forced assignments
        # Set Xiaomi Mi 11 at Carol's house
        base_phone_by_house = dict(forced_phones)
        carol_house = name_pos["Carol"]
        # If conflict (Carol's phone would overwrite gpixel6 or oneplus), skip
        if carol_house in base_phone_by_house and base_phone_by_house[carol_house] != "xiaomi mi 11":
            continue
        base_phone_by_house[carol_house] = "xiaomi mi 11"

        # Remaining phones to assign and houses
        remaining_phones = [p for p in Phones if p not in base_phone_by_house.values()]
        remaining_houses = [h for h in houses if h not in base_phone_by_house]

        # Iterate over permutations of remaining phones to the remaining houses with pruning
        for phones_perm in itertools.permutations(remaining_phones, len(remaining_houses)):
            phone_by_house = dict(base_phone_by_house)
            consistent = True
            for h, p in zip(remaining_houses, phones_perm):
                # Constraint 6: Samsung not in first house
                if h == 1 and p == "samsung galaxy s21":
                    consistent = False
                    break
                phone_by_house[h] = p
            if not consistent:
                continue

            phone_pos = {phone_by_house[h]: h for h in houses}

            # Constraint 2: Peter left of iPhone 13
            if not (name_pos["Peter"] < phone_pos["iphone 13"]):
                continue

            # Constraint 11: GP6 to the right of Eric (redundant but verify)
            if not (phone_pos["google pixel 6"] > name_pos["Eric"]):
                continue

            # Assign heights with forced ones
            height_by_house = dict(forced_heights)
            # Arnold is tall
            arnold_house = name_pos["Arnold"]
            if arnold_house in height_by_house and height_by_house[arnold_house] != "tall":
                continue
            height_by_house[arnold_house] = "tall"

            # Carol is very tall
            if carol_house in height_by_house and height_by_house[carol_house] != "very tall":
                continue
            height_by_house[carol_house] = "very tall"

            # Remaining height 'average' goes to the last unspecified house among 1..6
            remaining_height_houses = [h for h in houses if h not in height_by_house]
            # The only remaining height should be 'average' and exactly one house should be left (2,3,4 consist of tall, very tall, average)
            if len(remaining_height_houses) != 1:
                continue
            height_by_house[remaining_height_houses[0]] = "average"

            height_pos = {height_by_house[h]: h for h in houses}

            # Final verification of all clues
            if not check_all_clues(name_pos, height_pos, phone_pos):
                continue

            # Construct solution rows
            rows = []
            for h in houses:
                rows.append([str(h), house_to_name[h], height_by_house[h], phone_by_house[h]])

            solution = {
                "solution": {
                    "header": ["House", "Name", "Height", "PhoneModel"],
                    "rows": rows
                }
            }
            return solution

    raise ValueError("No solution found")

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))