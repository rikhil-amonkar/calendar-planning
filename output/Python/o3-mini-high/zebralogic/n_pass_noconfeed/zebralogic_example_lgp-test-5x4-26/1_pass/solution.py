#!/usr/bin/env python3
import itertools
import json

def valid(names, heights, mothers, hair):
    # Clue 1: The person who is tall is the person whose mother's name is Holly.
    for i in range(5):
        if heights[i] == "tall" and mothers[i] != "Holly":
            return False
        if mothers[i] == "Holly" and heights[i] != "tall":
            return False

    # Clue 2: There are two houses between the person who has an average height and the person who is short.
    try:
        idx_average = heights.index("average")
        idx_short = heights.index("short")
    except ValueError:
        return False
    if abs(idx_average - idx_short) != 3:
        return False

    # Clue 3: The person who has gray hair is directly left of the person whose mother's name is Janelle.
    if "gray" not in hair:
        return False
    idx_gray = hair.index("gray")
    if idx_gray == 4:
        return False
    if mothers[idx_gray + 1] != "Janelle":
        return False

    # Clue 4: The person who has black hair is not in the fourth house.
    if hair[3] == "black":
        return False

    # Clue 5: Eric is the person who has black hair.
    try:
        idx_eric = names.index("Eric")
    except ValueError:
        return False
    if hair[idx_eric] != "black":
        return False

    # Clue 6: The person who is very short is the person whose mother's name is Penny.
    for i in range(5):
        if heights[i] == "very short" and mothers[i] != "Penny":
            return False
        if mothers[i] == "Penny" and heights[i] != "very short":
            return False

    # Clue 7: Eric and the person who has gray hair are next to each other.
    if abs(idx_eric - idx_gray) != 1:
        return False

    # Clue 8: Bob is in the fifth house.
    if names[4] != "Bob":
        return False

    # Clue 9: The person who has red hair is Peter.
    if "red" not in hair:
        return False
    idx_red = hair.index("red")
    if names[idx_red] != "Peter":
        return False
    try:
        idx_peter = names.index("Peter")
    except ValueError:
        return False
    if hair[idx_peter] != "red":
        return False

    # Clue 10: The person whose mother's name is Kailyn is directly left of the person who is short.
    if "Kailyn" not in mothers:
        return False
    idx_kailyn = mothers.index("Kailyn")
    if idx_kailyn == 4:
        return False
    if heights[idx_kailyn + 1] != "short":
        return False

    # Clue 11: Arnold is the person who has brown hair.
    try:
        idx_arnold = names.index("Arnold")
    except ValueError:
        return False
    if hair[idx_arnold] != "brown":
        return False

    # Clue 12: The person who has brown hair is somewhere to the left of the person whose mother's name is Janelle.
    if "brown" not in hair or "Janelle" not in mothers:
        return False
    idx_brown = hair.index("brown")
    idx_janelle = mothers.index("Janelle")
    if idx_brown >= idx_janelle:
        return False

    # Clue 13: The person whose mother's name is Aniya and the person who is very short are next to each other.
    if "Aniya" not in mothers:
        return False
    idx_aniya = mothers.index("Aniya")
    if "very short" not in heights:
        return False
    idx_very_short = heights.index("very short")
    if abs(idx_aniya - idx_very_short) != 1:
        return False

    # Clue 14: The person whose mother's name is Kailyn is in the third house.
    if mothers[2] != "Kailyn":
        return False

    return True

def solve():
    names_all = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    # Bob is fixed in the fifth house, so consider the remaining for the other houses.
    names_except_bob = [name for name in names_all if name != "Bob"]
    
    mothers_all = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
    # The person with mother's name Kailyn is in the third house.
    mothers_remaining = [m for m in mothers_all if m != "Kailyn"]
    
    heights_all = ["very short", "short", "tall", "average", "very tall"]
    hair_all = ["blonde", "black", "gray", "red", "brown"]

    # Iterate over all candidate permutations with fixed positions as per clues.
    for names_perm in itertools.permutations(names_except_bob):
        # Build names with Bob in the fifth house.
        names = list(names_perm) + ["Bob"]
        for mothers_perm in itertools.permutations(mothers_remaining):
            # Assign mothers to houses 0,1,3,4; house 3 is fixed to Kailyn.
            mothers = [None] * 5
            free_indices = [0, 1, 3, 4]
            for i, idx in enumerate(free_indices):
                mothers[idx] = mothers_perm[i]
            mothers[2] = "Kailyn"
            for heights_perm in itertools.permutations(heights_all):
                heights = list(heights_perm)
                for hair_perm in itertools.permutations(hair_all):
                    hair = list(hair_perm)
                    if valid(names, heights, mothers, hair):
                        # Construct the solution dictionary in the required JSON structure.
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                                "rows": []
                            }
                        }
                        for i in range(5):
                            row = [str(i+1), names[i], heights[i], mothers[i], hair[i]]
                            solution["solution"]["rows"].append(row)
                        return solution
    return None

if __name__ == "__main__":
    sol = solve()
    print(json.dumps(sol))