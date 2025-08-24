import json
import itertools

def solve_puzzle():
    houses = [0, 1, 2, 3]  # indices for houses 1..4

    Names = ["Eric", "Peter", "Arnold", "Alice"]
    Smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    Cigars = ["blue master", "pall mall", "dunhill", "prince"]
    Heights = ["tall", "average", "short", "very short"]
    Phones = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    solutions = []

    # Iterate over phone arrangements first due to adjacency constraint
    for phone_perm in itertools.permutations(Phones):
        # 3. Samsung Galaxy S21 directly left of iPhone 13
        try:
            s_index = phone_perm.index("samsung galaxy s21")
            i_index = phone_perm.index("iphone 13")
        except ValueError:
            continue
        if s_index + 1 != i_index:
            continue

        # Heights permutations with constraints
        for height_perm in itertools.permutations(Heights):
            # 7. Tall in the third house (index 2)
            if height_perm[2] != "tall":
                continue
            # 8. Very short uses iPhone 13 (same person)
            if height_perm[i_index] != "very short":
                continue

            # Cigars permutations
            for cigar_perm in itertools.permutations(Cigars):
                # 9. Blue Master not in the first house (index 0)
                if cigar_perm[0] == "blue master":
                    continue
                # 10. Dunhill smoker is short (same person)
                try:
                    d_index = cigar_perm.index("dunhill")
                except ValueError:
                    continue
                if height_perm[d_index] != "short":
                    continue
                # 4. Dunhill is to the right of very short
                if d_index <= i_index:
                    continue
                # 6. Prince smoker uses OnePlus 9 (same person)
                try:
                    p_index = cigar_perm.index("prince")
                except ValueError:
                    continue
                if phone_perm[p_index] != "oneplus 9":
                    continue

                # Smoothies permutations
                for smoothie_perm in itertools.permutations(Smoothies):
                    # 2. Dunhill smoker likes Cherry (same person)
                    if smoothie_perm[d_index] != "cherry":
                        continue
                    # 5. Watermelon to the right of Desert
                    try:
                        desert_idx = smoothie_perm.index("desert")
                        water_idx = smoothie_perm.index("watermelon")
                    except ValueError:
                        continue
                    if not (water_idx > desert_idx):
                        continue
                    # 13. Dragonfruit lover is the Pall Mall smoker (same person)
                    try:
                        dragon_idx = smoothie_perm.index("dragonfruit")
                        pall_idx = cigar_perm.index("pall mall")
                    except ValueError:
                        continue
                    if dragon_idx != pall_idx:
                        continue

                    # Names permutations
                    for name_perm in itertools.permutations(Names):
                        # 1. Dragonfruit lover is Eric (same person)
                        if name_perm[dragon_idx] != "Eric":
                            continue
                        # 11. Peter not in the third house
                        if name_perm[2] == "Peter":
                            continue
                        # 12. Arnold uses Google Pixel 6 (same person)
                        try:
                            pixel_idx = phone_perm.index("google pixel 6")
                        except ValueError:
                            continue
                        if name_perm[pixel_idx] != "Arnold":
                            continue

                        # All constraints satisfied; record solution
                        solution = []
                        for h in houses:
                            solution.append({
                                "House": str(h + 1),
                                "Name": name_perm[h],
                                "Smoothie": smoothie_perm[h],
                                "Cigar": cigar_perm[h],
                                "Height": height_perm[h],
                                "PhoneModel": phone_perm[h],
                            })
                        solutions.append(solution)

    # Ensure unique solution
    if not solutions:
        raise RuntimeError("No solution found.")
    if len(solutions) > 1:
        # In case multiple solutions, pick the first but this puzzle should be unique.
        pass

    sol = solutions[0]
    # Build output JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": [
                [row["House"], row["Name"], row["Smoothie"], row["Cigar"], row["Height"], row["PhoneModel"]]
                for row in sol
            ],
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))