#!/usr/bin/env python3
import itertools
import json

def main():
    names_all = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    hair_all = ["auburn", "blonde", "brown", "black", "red", "gray"]
    height_all = ["very tall", "average", "very short", "tall", "super tall", "short"]

    # Fixed clues:
    # Clue 2: Alice is in the fourth house (index 3)
    # Clue 12: The person who has gray hair is in the third house (index 2)
    # Clue 10: The person who is very short is in the fifth house (index 4)
    # Clue 4: The person who is tall is in the sixth house (index 5)
    free_names = [n for n in names_all if n != "Alice"]
    free_hair = [h for h in hair_all if h != "gray"]
    free_heights = [ht for ht in height_all if ht not in ["very short", "tall"]]
    
    solution = None

    for names_perm in itertools.permutations(free_names, 5):
        # Create names list with Alice fixed in house 4 (index 3)
        names = [None] * 6
        names[0] = names_perm[0]
        names[1] = names_perm[1]
        names[2] = names_perm[2]
        names[3] = "Alice"
        names[4] = names_perm[3]
        names[5] = names_perm[4]
        
        # Clue 2 is satisfied by construction.
        for hair_perm in itertools.permutations(free_hair, 5):
            # Create hair list with gray fixed in house 3 (index 2)
            hair = [None] * 6
            hair[0] = hair_perm[0]
            hair[1] = hair_perm[1]
            hair[2] = "gray"
            hair[3] = hair_perm[2]
            hair[4] = hair_perm[3]
            hair[5] = hair_perm[4]
            
            # Clue 12 satisfied.
            for height_perm in itertools.permutations(free_heights, 4):
                # Create height list with very short at house5 (index 4) and tall at house6 (index 5)
                height = [None] * 6
                height[0] = height_perm[0]
                height[1] = height_perm[1]
                height[2] = height_perm[2]
                height[3] = height_perm[3]
                height[4] = "very short"
                height[5] = "tall"
                
                valid = True

                # Clue 1: The person who has blonde hair is directly left of Bob.
                if not any(hair[i] == "blonde" and names[i+1] == "Bob" for i in range(5)):
                    valid = False

                # Clue 3: The person who is short is Arnold.
                if "short" in height:
                    idx_short = height.index("short")
                    if names[idx_short] != "Arnold":
                        valid = False
                else:
                    valid = False

                # Clue 5: The person who has black hair is not in the fourth house (index 3).
                if hair[3] == "black":
                    valid = False

                # Clue 6: The person who has red hair is Eric.
                if "red" in hair:
                    idx_red = hair.index("red")
                    if names[idx_red] != "Eric":
                        valid = False
                else:
                    valid = False

                # Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
                if "average" in height and "super tall" in height:
                    idx_avg = height.index("average")
                    idx_super = height.index("super tall")
                    if idx_super <= idx_avg:
                        valid = False
                else:
                    valid = False

                # Clue 8: The person who has blonde hair is Carol.
                if "blonde" in hair:
                    idx_blonde = hair.index("blonde")
                    if names[idx_blonde] != "Carol":
                        valid = False
                else:
                    valid = False

                # Clue 9: There is one house between the person who has gray hair and the person who has red hair.
                # Gray hair is fixed in house 3 (index 2)
                if "red" in hair:
                    idx_red = hair.index("red")
                    if abs(2 - idx_red) != 2:
                        valid = False
                else:
                    valid = False

                # Clue 11: Bob is the person who has brown hair.
                if "Bob" in names:
                    idx_bob = names.index("Bob")
                    if hair[idx_bob] != "brown":
                        valid = False
                else:
                    valid = False

                # Clue 13: The person who has blonde hair is the person who is very tall.
                if "blonde" in hair:
                    idx_blonde = hair.index("blonde")
                    if height[idx_blonde] != "very tall":
                        valid = False
                else:
                    valid = False

                if valid:
                    solution = []
                    for i in range(6):
                        house = {
                            "House": str(i + 1),
                            "Name": names[i],
                            "Hair": hair[i],
                            "Height": height[i]
                        }
                        solution.append(house)
                    break
            if solution:
                break
        if solution:
            break

    if solution:
        output = {
            "solution": {
                "header": ["House", "Name", "Hair", "Height"],
                "rows": [[house["House"], house["Name"], house["Hair"], house["Height"]] for house in solution]
            }
        }
        print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()