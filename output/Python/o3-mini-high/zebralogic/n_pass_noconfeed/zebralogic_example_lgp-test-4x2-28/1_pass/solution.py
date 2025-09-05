import itertools
import json

def main():
    houses = [1, 2, 3, 4]  # House numbers
    names = ["Alice", "Arnold", "Peter", "Eric"]
    hair_colors = ["black", "blonde", "brown", "red"]
    
    # We will generate assignments for houses as a tuple of (name, hair_color)
    # with the following constraints:
    # 5. Alice is in the first house.
    # 2. Alice and Arnold are next to each other.
    # 3. Eric is the person who has brown hair.
    # 1. Eric is directly left of the person who has blonde hair.
    # 4. The person who has black hair is not in the first house.
    
    for name_perm in itertools.permutations(names):
        if name_perm[0] != "Alice":
            continue  # Clue 5: Alice is in the first house.
        # Clue 2: Alice and Arnold must be next to each other.
        idx_alice = 0  # since house 1 is fixed as Alice
        idx_arnold = name_perm.index("Arnold")
        if abs(idx_alice - idx_arnold) != 1:
            continue
        
        for hair_perm in itertools.permutations(hair_colors):
            # Clue 4: The person with black hair is not in the first house.
            if hair_perm[0] == "black":
                continue
            
            # Clue 3: Eric has brown hair.
            idx_eric = name_perm.index("Eric")
            if hair_perm[idx_eric] != "brown":
                continue
            
            # Clue 1: Eric is directly left of the person who has blonde hair.
            # Make sure Eric is not in the last house.
            if idx_eric == len(houses) - 1 or hair_perm[idx_eric + 1] != "blonde":
                continue
            
            # If all constraints are satisfied, then we have a valid solution.
            solution_rows = []
            for i in range(len(houses)):
                # House number as string, Name, HairColor
                solution_rows.append([str(houses[i]), name_perm[i], hair_perm[i]])
            
            result = {
                "solution": {
                    "header": ["House", "Name", "HairColor"],
                    "rows": solution_rows
                }
            }
            print(json.dumps(result))
            return  # Only output the first valid solution.

if __name__ == "__main__":
    main()