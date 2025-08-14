#!/usr/bin/env python3
import json
import itertools

def main():
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]
    
    # Houses will be indexed 0 to 4 corresponding to house 1 to 5.
    solution = None
    for perm_names in itertools.permutations(names):
        for perm_mothers in itertools.permutations(mothers):
            for perm_heights in itertools.permutations(heights):
                # Constraint 11: The person who is very short is in the fifth house.
                if perm_heights[4] != "very short":
                    continue

                valid = True
                for i in range(5):
                    name = perm_names[i]
                    mother = perm_mothers[i]
                    height = perm_heights[i]

                    # Clue 1: Alice is the person whose mother's name is Aniya.
                    if name == "Alice" and mother != "Aniya":
                        valid = False
                        break
                    # Clue 3: The person whose mother's name is Janelle is Bob.
                    if name == "Bob" and mother != "Janelle":
                        valid = False
                        break
                    # Clue 10: Eric is the person whose mother's name is Kailyn.
                    if name == "Eric" and mother != "Kailyn":
                        valid = False
                        break
                    # Clue 6: The person who is very tall is Arnold.
                    if name == "Arnold" and height != "very tall":
                        valid = False
                        break
                    # Deduction: Arnold cannot have mother Holly because then clue 9 fails,
                    # so Arnold must have mother Penny.
                    if name == "Arnold" and mother != "Penny":
                        valid = False
                        break
                    # Clue 8: Eric is not in the fifth house.
                    if i == 4 and name == "Eric":
                        valid = False
                        break
                    # Clue 4: Peter is not in the second house.
                    if i == 1 and name == "Peter":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 5: The person who is short is directly left of Arnold.
                try:
                    index_arnold = perm_names.index("Arnold")
                except ValueError:
                    continue
                if index_arnold == 0 or perm_heights[index_arnold - 1] != "short":
                    continue

                # Clue 7: Bob is directly left of the person who has an average height.
                try:
                    index_bob = perm_names.index("Bob")
                except ValueError:
                    continue
                if index_bob == 4 or perm_heights[index_bob + 1] != "average":
                    continue

                # Clue 2: The person who has an average height is somewhere to the left of 
                # the person whose mother's name is Penny (Arnold).
                try:
                    index_average = perm_heights.index("average")
                    index_penny = perm_mothers.index("Penny")
                except ValueError:
                    continue
                if index_average >= index_penny:
                    continue

                # Clue 9: The person who is very tall is somewhere to the right of 
                # the person whose mother's name is Holly.
                try:
                    index_very_tall = perm_heights.index("very tall")
                    index_holly = perm_mothers.index("Holly")
                except ValueError:
                    continue
                if index_holly >= index_very_tall:
                    continue

                # All constraints are satisfied; record the solution.
                sol_rows = []
                for i in range(5):
                    house_num = str(i + 1)
                    sol_rows.append([house_num, perm_names[i], perm_mothers[i], perm_heights[i]])
                solution = sol_rows
                break
            if solution is not None:
                break
        if solution is not None:
            break

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()