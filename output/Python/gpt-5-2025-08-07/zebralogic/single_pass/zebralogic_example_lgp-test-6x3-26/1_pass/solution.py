import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
    phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    def pos_of(value, arr):
        return arr.index(value) + 1

    solution = None

    for name_perm in permutations(names):
        # Map names by house (1..6)
        names_by_house = list(name_perm)
        pos_name = {name: i + 1 for i, name in enumerate(names_by_house)}

        # Clue 1 + 8: Bob is directly left of the person who is tall (tall is Arnold)
        if not (pos_name["Bob"] + 1 == pos_name["Arnold"]):
            continue

        # Prepare height assignment with constraints
        base_heights = [None] * 6

        def set_height(idx, val):
            if base_heights[idx] is not None and base_heights[idx] != val:
                return False
            base_heights[idx] = val
            return True

        # Clue 9: super tall is in the first house
        if not set_height(0, "super tall"):
            continue
        # Clue 12: short is in the sixth house
        if not set_height(5, "short"):
            continue
        # Clue 8: tall is Arnold
        if not set_height(pos_name["Arnold"] - 1, "tall"):
            continue
        # Clue 4: Carol is very tall
        if not set_height(pos_name["Carol"] - 1, "very tall"):
            continue

        # Fill remaining heights (must be permutation of remaining set)
        used_heights = [h for h in base_heights if h is not None]
        remaining_heights = [h for h in heights if h not in used_heights]
        remaining_positions = [i for i, h in enumerate(base_heights) if h is None]

        # Try all assignments of remaining heights
        for rem_assign in permutations(remaining_heights, len(remaining_positions)):
            heights_by_house = base_heights[:]
            for idx, hval in zip(remaining_positions, rem_assign):
                heights_by_house[idx] = hval

            # Now apply phone constraints
            # Build base phone mapping
            # We'll place fixed phones from constraints then permute the rest

            # Helper to assign phone with conflict check
            def assign_phone(pb, house_idx, phone_val):
                if pb[house_idx] is not None and pb[house_idx] != phone_val:
                    return None
                new_pb = pb[:]
                new_pb[house_idx] = phone_val
                return new_pb

            # Initialize phones by house
            phones_by_house_initial = [None] * 6

            # Clue 7: OnePlus 9 is directly left of the person who is short
            pos_short = pos_of("short", heights_by_house)
            pos_oneplus = pos_short - 1
            if not (1 <= pos_oneplus <= 6):
                continue
            pb = assign_phone(phones_by_house_initial, pos_oneplus - 1, "oneplus 9")
            if pb is None:
                continue

            # Clue 5: One house between Google Pixel 6 and the person who is short
            candidates_pixel = []
            for cand in (pos_short - 2, pos_short + 2):
                if 1 <= cand <= 6:
                    candidates_pixel.append(cand)

            for pos_pixel in candidates_pixel:
                pb_pixel = assign_phone(pb, pos_pixel - 1, "google pixel 6")
                if pb_pixel is None:
                    continue

                # Clue 3: very short is somewhere to the right of the person who uses a Google Pixel 6
                if pos_of("very short", heights_by_house) <= pos_pixel:
                    continue

                # Clue 10: Xiaomi Mi 11 is Carol
                pos_carol = pos_name["Carol"]
                pb_xiaomi = assign_phone(pb_pixel, pos_carol - 1, "xiaomi mi 11")
                if pb_xiaomi is None:
                    continue

                # Remaining phones to assign
                used_phones = set(p for p in pb_xiaomi if p is not None)
                remaining_phone_vals = [p for p in phones if p not in used_phones]
                remaining_phone_positions = [i for i, p in enumerate(pb_xiaomi) if p is None]

                for phone_assign in permutations(remaining_phone_vals, len(remaining_phone_positions)):
                    pb_full = pb_xiaomi[:]
                    for idx, pval in zip(remaining_phone_positions, phone_assign):
                        pb_full[idx] = pval

                    # Check all phone-related constraints
                    # Clue 6: Samsung Galaxy S21 is not in the first house
                    if pos_of("samsung galaxy s21", pb_full) == 1:
                        continue

                    # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13
                    if not (pos_name["Peter"] < pos_of("iphone 13", pb_full)):
                        continue

                    # Clue 11: Google Pixel 6 is somewhere to the right of Eric
                    if not (pos_of("google pixel 6", pb_full) > pos_name["Eric"]):
                        continue

                    # All constraints satisfied, construct solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "PhoneModel"],
                            "rows": []
                        }
                    }
                    for house in houses:
                        row = [
                            str(house),
                            names_by_house[house - 1],
                            heights_by_house[house - 1],
                            pb_full[house - 1]
                        ]
                        solution["solution"]["rows"].append(row)
                    return solution

    return None

def main():
    result = solve()
    if result is None:
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": []
            }
        }
    print(json.dumps(result))

if __name__ == "__main__":
    main()