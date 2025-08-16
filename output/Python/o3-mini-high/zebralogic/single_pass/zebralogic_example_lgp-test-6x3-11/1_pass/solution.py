#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
    heights_all = ["very tall", "average", "very short", "tall", "super tall", "short"]
    
    # Fixed positions from clues:
    # House 4 (index 3) must be "Alice"
    # House 5 (index 4) height is "very short"
    # House 6 (index 5) height is "tall"
    # House 3 (index 2) hair is "gray"
    # Also, hair in house 4 (index 3) cannot be "black"
    
    # For heights, remove fixed ones for houses 5 and 6.
    remaining_heights = [h for h in heights_all if h not in ["very short", "tall"]]
    # remaining_heights should be: ["very tall", "average", "super tall", "short"]
    
    solution = None
    
    for names_perm in itertools.permutations(names):
        # Clue 2: Alice is in the fourth house.
        if names_perm[3] != "Alice":
            continue
        
        for hair_perm in itertools.permutations(hair_colors):
            # Clue 12: The person who has gray hair is in the third house.
            if hair_perm[2] != "gray":
                continue
            # Clue 5: The person who has black hair is not in the fourth house.
            if hair_perm[3] == "black":
                continue
            
            for heights_perm in itertools.permutations(remaining_heights):
                # Construct full heights: houses 1-4 from heights_perm, then house 5 is "very short", house 6 is "tall".
                candidate_heights = heights_perm + ("very short", "tall")
                
                valid = True
                
                # Clue 1 & 13: The person who has blonde hair (Carol) is directly left of Bob
                # and the person with blonde hair is very tall.
                try:
                    index_blonde = hair_perm.index("blonde")
                except ValueError:
                    valid = False
                    continue
                if index_blonde == 5 or names_perm[index_blonde + 1] != "Bob":
                    valid = False
                if candidate_heights[index_blonde] != "very tall":
                    valid = False
                if not valid:
                    continue

                # Clues linking names and hair:
                # Clue 11: Bob is the person who has brown hair.
                # Clue 6: The person who has red hair is Eric.
                # Clue 8: The person who has blonde hair is Carol.
                for i, name in enumerate(names_perm):
                    if name == "Bob" and hair_perm[i] != "brown":
                        valid = False
                        break
                    if name == "Eric" and hair_perm[i] != "red":
                        valid = False
                        break
                    if name == "Carol" and hair_perm[i] != "blonde":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 3: The person who is short is Arnold.
                for i, name in enumerate(names_perm):
                    if name == "Arnold" and candidate_heights[i] != "short":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 9: There is one house between the person who has gray hair and the person who has red hair.
                try:
                    index_red = hair_perm.index("red")
                except ValueError:
                    valid = False
                    continue
                if abs(2 - index_red) != 2:
                    valid = False
                    continue
                
                # Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
                try:
                    index_average = candidate_heights.index("average")
                    index_super_tall = candidate_heights.index("super tall")
                except ValueError:
                    valid = False
                    continue
                if not (index_average < index_super_tall):
                    valid = False
                    continue

                if valid:
                    solution = []
                    for i in range(6):
                        house_number = str(i + 1)
                        row = [house_number, names_perm[i], hair_perm[i], candidate_heights[i]]
                        solution.append(row)
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()