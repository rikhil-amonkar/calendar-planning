#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    # There are 6 houses (indices 0 to 5)
    # Fixed names based on constraints:
    # Clue 3: Eric is in the second house => index 1 is "Eric"
    # Clue 7 & 4: The person who goes on cultural tours (Peter) is in the third house => index 2 is "Peter"
    # Clue 2: Eric is to the right of Alice, so with Eric in house2, Alice must be in house1 (index 0)
    names_fixed = ["Alice", "Eric", "Peter"]
    # The remaining names for houses 4,5,6 (indices 3,4,5)
    remaining_names = ["Bob", "Carol", "Arnold"]
    
    # Possible vacation types:
    vacations_all = ["mountain", "camping", "cruise", "city", "cultural", "beach"]
    # Fixed vacations:
    # Clue 4: House3 (index 2) is cultural
    # Clue 9: House4 (index 3) is city
    fixed_vac_indices = {2: "cultural", 3: "city"}
    # The remaining vacation types for houses indices 0,1,4,5:
    remaining_vacs = [v for v in vacations_all if v not in fixed_vac_indices.values()]
    
    solution = None

    # Iterate through assignments for names in houses 4,5,6.
    for perm_names in itertools.permutations(remaining_names):
        # Construct full names assignment for houses 1 to 6.
        names = names_fixed + list(perm_names)
        # Clue 5: Bob is directly left of Arnold.
        # Check if Bob appears immediately followed by Arnold.
        bob_left_of_arnold = any(names[i] == "Bob" and names[i+1] == "Arnold" for i in range(len(names)-1))
        if not bob_left_of_arnold:
            continue

        # Now iterate through assignments for vacations in houses 1,2,5,6 (indices 0,1,4,5).
        for perm_vac in itertools.permutations(remaining_vacs):
            vac = [None] * 6
            vac[0] = perm_vac[0]
            vac[1] = perm_vac[1]
            vac[2] = "cultural"  # fixed (clue 4)
            vac[3] = "city"      # fixed (clue 9)
            vac[4] = perm_vac[2]
            vac[5] = perm_vac[3]
            
            # Clue 6: The person who enjoys camping is not in the first house.
            if vac[0] == "camping":
                continue
            # Clue 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations.
            # Since cultural is at index 2, beach must be in one of the houses to its right.
            if "beach" not in vac or vac.index("beach") <= 2:
                continue
            # Clue 8: The person who likes cruises is Bob.
            index_bob = names.index("Bob")
            if vac[index_bob] != "cruise":
                continue

            # All constraints satisfied for this assignment.
            solution = {"names": names, "vacations": vac}
            break
        if solution is not None:
            break

    return solution

def main():
    sol = solve_puzzle()
    if sol is None:
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": []
            }
        }
    else:
        rows = []
        for i in range(6):
            house_number = str(i+1)
            name = sol["names"][i]
            vacation = sol["vacations"][i]
            rows.append([house_number, name, vacation])
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
    print(json.dumps(output))

if __name__ == '__main__':
    main()