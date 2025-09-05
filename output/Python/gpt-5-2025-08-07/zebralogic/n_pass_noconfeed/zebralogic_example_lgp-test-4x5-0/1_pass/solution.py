import itertools
import json

def solve_puzzle():
    houses = [0, 1, 2, 3]  # indices for houses 1..4

    # Categories
    Names = ["Eric", "Peter", "Arnold", "Alice"]
    Smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    Cigars = ["blue master", "pall mall", "dunhill", "prince"]
    Heights = ["tall", "average", "short", "very short"]
    Phones = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    solutions = []

    # Heights: fix "tall" at house 3 (index 2)
    remaining_heights = ["average", "short", "very short"]
    for perm in itertools.permutations(remaining_heights):
        heights = [None] * 4
        heights[2] = "tall"  # clue 7
        # Fill indices 0,1,3 with permutation
        fill_indices = [0, 1, 3]
        for idx, val in zip(fill_indices, perm):
            heights[idx] = val

        # iPhone (very short) cannot be at house 1 due to "Samsung directly left"
        idx_very_short = heights.index("very short")
        if idx_very_short == 0:
            continue

        # Dunhill smoker (short) is to the right of very short
        idx_short = heights.index("short")
        if idx_short <= idx_very_short:
            continue

        # Phones: Samsung directly left of iPhone; very short uses iPhone
        # Set iPhone and Samsung positions
        phones_base = [None] * 4
        phones_base[idx_very_short] = "iphone 13"  # clue 8
        left_idx = idx_very_short - 1
        phones_base[left_idx] = "samsung galaxy s21"  # clue 3

        # Remaining phones are Pixel 6 and OnePlus 9
        remaining_phone_positions = [i for i in houses if phones_base[i] is None]
        for phone_perm in itertools.permutations(["google pixel 6", "oneplus 9"]):
            phones = phones_base[:]
            for pos, val in zip(remaining_phone_positions, phone_perm):
                phones[pos] = val

            # Prince smoker uses OnePlus 9
            idx_oneplus = phones.index("oneplus 9")  # clue 6

            # Cigars: short -> Dunhill; OnePlus -> Prince; Blue Master not in house 1
            cigars = [None] * 4
            # If OnePlus and short at same house -> impossible (would need two cigars)
            if idx_oneplus == idx_short:
                continue
            cigars[idx_short] = "dunhill"  # clues 10
            cigars[idx_oneplus] = "prince"  # clue 6
            remaining_cigar_positions = [i for i in houses if cigars[i] is None]
            for cigar_perm in itertools.permutations(["blue master", "pall mall"]):
                cigars_try = cigars[:]
                valid_cigars = True
                for pos, val in zip(remaining_cigar_positions, cigar_perm):
                    cigars_try[pos] = val
                # Blue Master not in first house
                if cigars_try[0] == "blue master":  # clue 9
                    valid_cigars = False
                if not valid_cigars:
                    continue

                # Smoothies: short/Dunhill likes Cherry; Pall Mall <-> Dragonfruit; Watermelon right of Desert
                smoothies = [None] * 4
                smoothies[idx_short] = "cherry"  # clues 2 + 10
                idx_pallmall = cigars_try.index("pall mall")
                smoothies[idx_pallmall] = "dragonfruit"  # clues 1 + 13 combined later with Eric

                remaining_smoothie_positions = [i for i in houses if smoothies[i] is None]
                for smoothie_perm in itertools.permutations(["desert", "watermelon"]):
                    smoothies_try = smoothies[:]
                    for pos, val in zip(remaining_smoothie_positions, smoothie_perm):
                        smoothies_try[pos] = val
                    # Watermelon right of Desert
                    if smoothies_try.index("watermelon") <= smoothies_try.index("desert"):  # clue 5
                        continue

                    # Names: Arnold uses Pixel 6; Eric is Dragonfruit (and Pall Mall); Peter not in house 3
                    names = [None] * 4
                    idx_pixel = phones.index("google pixel 6")
                    names[idx_pixel] = "Arnold"  # clue 12
                    idx_dragonfruit = smoothies_try.index("dragonfruit")
                    # Ensure Pall Mall is also at dragonfruit (already by construction)
                    if cigars_try[idx_dragonfruit] != "pall mall":
                        continue
                    names[idx_dragonfruit] = "Eric"  # clues 1 + 13

                    if names[idx_pixel] == "Eric":
                        # Can't be both Arnold and Eric
                        continue

                    remaining_name_positions = [i for i in houses if names[i] is None]
                    for name_perm in itertools.permutations(["Peter", "Alice"]):
                        names_try = names[:]
                        valid_names = True
                        for pos, val in zip(remaining_name_positions, name_perm):
                            names_try[pos] = val
                        # Peter not in third house
                        if names_try[2] == "Peter":  # clue 11
                            valid_names = False
                        if not valid_names:
                            continue

                        # Final consistency checks (redundant but safe)
                        # Tall is house 3 (already enforced)
                        if heights[2] != "tall":
                            continue
                        # Ensure all sets are unique per house
                        if not (len(set(names_try)) == len(set(smoothies_try)) == len(set(cigars_try)) == len(set(heights)) == len(set(phones)) == 4):
                            continue

                        solutions.append({
                            "names": names_try,
                            "smoothies": smoothies_try,
                            "cigars": cigars_try,
                            "heights": heights[:],
                            "phones": phones[:],
                        })

    # Expect a unique solution
    if not solutions:
        raise RuntimeError("No solution found")
    # If multiple, pick the first
    sol = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": []
        }
    }
    for i in range(4):
        row = [
            str(i + 1),
            sol["names"][i],
            sol["smoothies"][i],
            sol["cigars"][i],
            sol["heights"][i],
            sol["phones"][i],
        ]
        output["solution"]["rows"].append(row)

    return output


if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))