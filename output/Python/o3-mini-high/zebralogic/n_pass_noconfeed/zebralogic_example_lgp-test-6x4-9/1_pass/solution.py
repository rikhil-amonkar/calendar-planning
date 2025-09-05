import itertools
import json

def solve():
    # Define the options for each attribute.
    names_origin = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    phones_origin = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    nats_origin = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    colors_origin = ["blue", "red", "yellow", "green", "white", "purple"]
    
    # We'll use 0-index for houses: house number = index+1.
    # The clues:
    # 1. Carol is not in the third house (index 2).
    # 2. There is one house between the Dane and the British person.
    # 3. Carol's favorite color is green.
    # 4. Arnold is directly left of Alice.
    # 5. Alice is the German.
    # 6. The person who uses OnePlus 9 is the person who loves purple.
    # 7. The person who uses Huawei P50 is not in the third house (index 2).
    # 8. Samsung Galaxy S21 is in the fifth house (index 4).
    # 9. The person who loves white is somewhere to the right of the person whose favorite color is red.
    # 10. The person who uses Samsung Galaxy S21 is Bob.
    # 11. The Dane is the person who loves yellow.
    # 12. The person who uses Samsung Galaxy S21 is somewhere to the left of Peter.
    # 13. The person who loves blue is Peter.
    # 14. Peter is the British person.
    # 15. Samsung Galaxy S21 is directly left of iPhone 13.
    # 16. The Norwegian is the person who loves purple.
    # 17. The person who uses Xiaomi Mi 11 is the Chinese.
    
    # We will iterate over possible assignments for the six houses.
    solution_found = None

    # 1. Assign names. Enforce:
    #   - House 5 (index 4) must be Bob because clue 10 and 8.
    #   - House 6 (index 5) must be Peter because of clue 12 and 14.
    #   - Carol cannot be in the third house (index 2).
    #   - Arnold is directly left of Alice.
    for names_perm in itertools.permutations(names_origin):
        if names_perm[4] != "Bob" or names_perm[5] != "Peter":
            continue
        if names_perm[2] == "Carol":
            continue
        # Check for "Arnold is directly left of Alice"
        if not any(names_perm[i] == "Arnold" and i+1 < 6 and names_perm[i+1] == "Alice" for i in range(6)):
            continue

        # 2. Assign phone models.
        # Fixed: House 5 (index 4) is "samsung galaxy s21" (clue 8) and House 6 (index 5) is "iphone 13" (clue 15).
        fixed_phones = {"samsung galaxy s21", "iphone 13"}
        free_phones = [p for p in phones_origin if p not in fixed_phones]
        for free_perm in itertools.permutations(free_phones):
            phones = [None] * 6
            phones[0], phones[1], phones[2], phones[3] = free_perm
            phones[4] = "samsung galaxy s21"
            phones[5] = "iphone 13"
            # Clue 7: Huawei P50 is not in the third house (index 2)
            if phones[2] == "huawei p50":
                continue

            # 3. Assign nationalities.
            # Fixed by clues:
            #   - If name is Alice then she is German (clue 5).
            #   - If name is Peter then he is British (clue 14).
            #   - Clue 2: With the British person in house 6 (index 5), the Dane must be two houses away.
            #     The only possibility is house 4 (index 3) must be the Dane since 5 - 3 = 2.
            nat = [None] * 6
            fixed_nat = {}
            for i in range(6):
                if names_perm[i] == "Alice":
                    nat[i] = "german"
                    fixed_nat[i] = "german"
                if names_perm[i] == "Peter":
                    nat[i] = "brit"
                    fixed_nat[i] = "brit"
            nat[3] = "dane"  # House 4 must be Dane (clue 2 and 11)
            fixed_nat[3] = "dane"
            # The remaining houses (indices not in fixed_nat) must get a permutation of the remaining nationalities.
            remaining_nats = [n for n in nats_origin if n not in fixed_nat.values()]
            unfixed_nat_idx = [i for i in range(6) if i not in fixed_nat]
            for nat_perm in itertools.permutations(remaining_nats):
                for idx, nat_val in zip(unfixed_nat_idx, nat_perm):
                    nat[idx] = nat_val
                # Additional constraints from phones and nationalities:
                valid_nat = True
                for i in range(6):
                    # Clue 17: The person who uses Xiaomi Mi 11 is the Chinese.
                    if nat[i] == "chinese" and phones[i] != "xiaomi mi 11":
                        valid_nat = False
                        break
                    # Clue 16 (and 6): The Norwegian loves purple and uses OnePlus 9.
                    if nat[i] == "norwegian" and phones[i] != "oneplus 9":
                        valid_nat = False
                        break
                # Also, Bob is in house 5 (index 4); if Bob were chinese or norwegian,
                # the phone condition would force xiaomi mi 11 or oneplus 9, but house 5 has samsung galaxy s21.
                if nat[4] in {"chinese", "norwegian"}:
                    valid_nat = False
                if not valid_nat:
                    continue

                # 4. Assign colors.
                # Fixed by clues:
                #   - Carol loves green (clue 3).
                #   - Peter loves blue (clue 13).
                #   - The Dane loves yellow (clue 11).
                #   - The Norwegian loves purple (clue 16).
                colors = [None] * 6
                fixed_colors = {}
                for i in range(6):
                    if names_perm[i] == "Carol":
                        colors[i] = "green"
                        fixed_colors[i] = "green"
                    if names_perm[i] == "Peter":
                        colors[i] = "blue"
                        fixed_colors[i] = "blue"
                    if nat[i] == "dane":
                        colors[i] = "yellow"
                        fixed_colors[i] = "yellow"
                    if nat[i] == "norwegian":
                        colors[i] = "purple"
                        fixed_colors[i] = "purple"
                # The remaining colors to assign (they must be unique)
                remaining_colors = [c for c in colors_origin if c not in fixed_colors.values()]
                unfixed_color_idx = [i for i in range(6) if i not in fixed_colors]
                for color_perm in itertools.permutations(remaining_colors):
                    for idx, col in zip(unfixed_color_idx, color_perm):
                        colors[idx] = col
                    # Clue 9: The person who loves white is somewhere to the right of the person who loves red.
                    try:
                        pos_red = colors.index("red")
                        pos_white = colors.index("white")
                    except ValueError:
                        continue
                    if pos_red >= pos_white:
                        continue
                    # Clue 6: The person who uses OnePlus 9 is the person who loves purple.
                    valid_color = True
                    for i in range(6):
                        if colors[i] == "purple" and phones[i] != "oneplus 9":
                            valid_color = False
                            break
                    if not valid_color:
                        continue

                    # All constraints satisfied: Save this solution.
                    solution_rows = []
                    for i in range(6):
                        # House numbers are string representations of index+1
                        solution_rows.append([str(i+1), names_perm[i], phones[i], nat[i], colors[i]])
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(solution, indent=2))
                    return

if __name__ == "__main__":
    solve()