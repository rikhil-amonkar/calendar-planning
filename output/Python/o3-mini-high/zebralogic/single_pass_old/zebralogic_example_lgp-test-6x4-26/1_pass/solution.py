#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    # Define all possible attributes.
    names_all = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
    # Birthday months exactly as given.
    birthdays_all = ["mar", "sept", "may", "feb", "jan", "april"]
    # House styles.
    styles_all = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
    # Pets.
    pets_all = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
    
    # We know from the clues the following fixed placements:
    # Clue 5: Carol is in the third house  --> names[2] == "Carol"
    # Clue 8: Eric is in the sixth house    --> names[5] == "Eric"
    # Clue 14: Peter is in the colonial house, and
    # Clue 4: The colonial-style house is in the second house  --> names[1] must be Peter and styles[1] == "colonial"
    # Clue 18 & 11: The craftsman house is in the fourth house and that person is Arnold --> names[3] == "Arnold", styles[3] == "craftsman"
    # Thus for names, the remaining two houses (first and fifth) must be Bob and Alice.
    # For birthdays:
    # Clue 3: House 2 has birthday "may"       --> birthdays[1] == "may"
    # Clue 17: Carol's birthday is "mar"         --> birthdays[2] == "mar"
    # Clue 15: "jan" is directly left of "april"   --> in whichever house "jan" appears, the next house must be "april".
    # Clue 2: "jan" is somewhere to the left of "sept"  --> index(jan) < index(sept)
    # For pets:
    # Clue 19: House 4 has pet "dog"              --> pets[3] == "dog"
    # Clue 13: The fish is not in the second house  --> pets[1] != "fish"
    # For styles:
    # Clue 4 & 14: House 2 is "colonial"           --> styles[1] == "colonial"
    # Clue 18 & 11: House 4 is "craftsman"           --> styles[3] == "craftsman"
    # Clue 6: Mediterranean is not in house 6       --> styles[5] != "mediterranean"
    # Clue 12: The colonial house must be to the left of the modern house --> index("colonial") < index("modern")
    
    solution_found = None
    
    # Iterate over names permutations.
    for names_perm in itertools.permutations(names_all):
        # Enforce fixed names.
        if names_perm[1] != "Peter" or names_perm[2] != "Carol" or names_perm[3] != "Arnold" or names_perm[5] != "Eric":
            continue
        # The remaining two (house 1 and house 5) must be Bob and Alice.
        if set([names_perm[0], names_perm[4]]) != set(["Bob", "Alice"]):
            continue
        
        # Iterate over birthdays permutations.
        for bdays_perm in itertools.permutations(birthdays_all):
            if bdays_perm[1] != "may" or bdays_perm[2] != "mar":
                continue
            # Clue 15: The birthday "jan" must be immediately left of "april".
            jan_index = bdays_perm.index("jan")
            if jan_index == 5 or bdays_perm[jan_index + 1] != "april":
                continue
            # Clue 2: "jan" must be to the left of "sept".
            if bdays_perm.index("jan") >= bdays_perm.index("sept"):
                continue

            # Iterate over styles permutations.
            for styles_perm in itertools.permutations(styles_all):
                if styles_perm[1] != "colonial" or styles_perm[3] != "craftsman":
                    continue
                if styles_perm[5] == "mediterranean":
                    continue
                # Clue 12: "colonial" must be left of "modern".
                if styles_perm.index("colonial") >= styles_perm.index("modern"):
                    continue
                
                # Iterate over pets permutations.
                for pets_perm in itertools.permutations(pets_all):
                    if pets_perm[3] != "dog":
                        continue
                    if pets_perm[1] == "fish":  # Clue 13: fish is not in the second house.
                        continue

                    # Now check the cross-category constraints:
                    # Clue 1: The pet hamster is somewhere to the right of the house whose birthday is in March.
                    if pets_perm.index("hamster") <= bdays_perm.index("mar"):
                        continue
                    # Clue 7: The fish is somewhere to the right of Bob.
                    if pets_perm.index("fish") <= names_perm.index("Bob"):
                        continue
                    # Clue 9: There is one house between the cat and the Victorian house.
                    if abs(pets_perm.index("cat") - styles_perm.index("victorian")) != 2:
                        continue
                    # Clue 10: There are two houses between the Victorian house and the hamster.
                    if abs(pets_perm.index("hamster") - styles_perm.index("victorian")) != 3:
                        continue
                    # Clue 16: There is one house between the pet bird and the modern house.
                    if abs(pets_perm.index("bird") - styles_perm.index("modern")) != 2:
                        continue

                    # All constraints are satisfied; record this solution.
                    solution_found = {
                        "names": names_perm,
                        "birthdays": bdays_perm,
                        "styles": styles_perm,
                        "pets": pets_perm
                    }
                    break
                if solution_found is not None:
                    break
            if solution_found is not None:
                break
        if solution_found is not None:
            break

    return solution_found

def main():
    sol = solve_puzzle()
    if sol is None:
        result = {"solution": {"header": [], "rows": []}}
    else:
        # Build rows: each row is [House, Name, pet, style, birthday]
        rows = []
        # There are 6 houses (indexed 0...5 corresponds to House 1...6)
        for i in range(6):
            row = [
                str(i + 1),
                sol["names"][i],
                sol["pets"][i],
                sol["styles"][i],
                sol["birthdays"][i]
            ]
            rows.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "pet", "style", "birthday"],
                "rows": rows
            }
        }
    print(json.dumps(result))

if __name__ == '__main__':
    main()