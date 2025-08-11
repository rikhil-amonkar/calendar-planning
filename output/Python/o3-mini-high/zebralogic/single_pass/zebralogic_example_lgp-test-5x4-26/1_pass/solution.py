#!/usr/bin/env python3
import itertools
import json

def main():
    # Define possible attributes
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    heights = ["very short", "short", "tall", "average", "very tall"]
    mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
    hair_colors = ["blonde", "black", "gray", "red", "brown"]

    # To reduce search space use the following fixed clues:
    # Clue 8: Bob is in the fifth house => names[4] must be "Bob"
    # Clue 14: The person whose mother's name is Kailyn is in the third house => mothers[2] == "Kailyn"
    # Clue 2 & Clue 10 (with Clue 14) force:
    #  - There are two houses between the person with average height and the person who is short.
    #  - Using Clue 10: the person whose mother's name is Kailyn is directly left of the person who is short.
    #    Since mothers[2] is "Kailyn", the house to its right (index 3) must be short.
    #  - Then Clue 2 forces the average height to be in the first house (index 0) because |0 - 3| = 3.
    
    # So we set fixed positions for heights:
    # House 1 (index 0): "average"
    # House 4 (index 3): "short"
    # The remaining houses (indices 1,2,4) must get the leftover heights from {"very short", "tall", "very tall"}.
    remaining_heights = ["very short", "tall", "very tall"]
    
    solution_found = False
    # Iterate over assignments for the unfixed heights for houses 2,3,5 (indices 1,2,4)
    for perm_heights in itertools.permutations(remaining_heights):
        candidate_heights = [None] * 5
        candidate_heights[0] = "average"   # House 1 fixed
        candidate_heights[3] = "short"       # House 4 fixed
        candidate_heights[1] = perm_heights[0]
        candidate_heights[2] = perm_heights[1]
        candidate_heights[4] = perm_heights[2]
        
        # Iterate over mothers permutations; must satisfy clue 14: mother's in house 3 (index 2) is "Kailyn".
        for perm_mothers in itertools.permutations(mothers):
            if perm_mothers[2] != "Kailyn":
                continue
            candidate_mothers = list(perm_mothers)
            
            # Iterate over names permutations; clue 8: House 5 (index 4) is "Bob".
            for perm_names in itertools.permutations(names):
                if perm_names[4] != "Bob":
                    continue
                candidate_names = list(perm_names)
                
                # Iterate over hair color permutations.
                for perm_hair in itertools.permutations(hair_colors):
                    candidate_hair = list(perm_hair)
                    
                    # Now check all the clues:
                    # Clue 1: The person who is tall is the person whose mother's name is Holly.
                    try:
                        index_tall = candidate_heights.index("tall")
                    except ValueError:
                        continue
                    if candidate_mothers[index_tall] != "Holly":
                        continue
                    
                    # Clue 2: There are two houses between the person who has an average height and the person who is short.
                    index_avg = candidate_heights.index("average")
                    index_short = candidate_heights.index("short")
                    if abs(index_avg - index_short) != 3:
                        continue
                    
                    # Clue 3: The person who has gray hair is directly left of the person whose mother's name is Janelle.
                    try:
                        index_gray = candidate_hair.index("gray")
                    except ValueError:
                        continue
                    if index_gray == 4 or candidate_mothers[index_gray + 1] != "Janelle":
                        continue
                    
                    # Clue 4: The person who has black hair is not in the fourth house (index 3).
                    if candidate_hair[3] == "black":
                        continue
                    
                    # Clue 5: Eric is the person who has black hair.
                    try:
                        index_eric = candidate_names.index("Eric")
                    except ValueError:
                        continue
                    if candidate_hair[index_eric] != "black":
                        continue
                    
                    # Clue 6: The person who is very short is the person whose mother's name is Penny.
                    try:
                        index_vshort = candidate_heights.index("very short")
                    except ValueError:
                        continue
                    if candidate_mothers[index_vshort] != "Penny":
                        continue
                    
                    # Clue 7: Eric and the person who has gray hair are next to each other.
                    if abs(index_eric - index_gray) != 1:
                        continue
                    
                    # Clue 8: Bob is in the fifth house (already enforced).
                    if candidate_names[4] != "Bob":
                        continue
                    
                    # Clue 9: The person who has red hair is Peter.
                    try:
                        index_red = candidate_hair.index("red")
                    except ValueError:
                        continue
                    if candidate_names[index_red] != "Peter":
                        continue
                    
                    # Clue 10: The person whose mother's name is Kailyn is directly left of the person who is short.
                    try:
                        index_kailyn = candidate_mothers.index("Kailyn")
                    except ValueError:
                        continue
                    if index_kailyn == 4 or candidate_heights[index_kailyn + 1] != "short":
                        continue
                    
                    # Clue 11: Arnold is the person who has brown hair.
                    try:
                        index_arnold = candidate_names.index("Arnold")
                    except ValueError:
                        continue
                    if candidate_hair[index_arnold] != "brown":
                        continue
                    
                    # Clue 12: The person who has brown hair is somewhere to the left of the person whose mother's name is Janelle.
                    try:
                        index_brown = candidate_hair.index("brown")
                        index_janelle = candidate_mothers.index("Janelle")
                    except ValueError:
                        continue
                    if not (index_brown < index_janelle):
                        continue
                    
                    # Clue 13: The person whose mother's name is Aniya and the person who is very short are next to each other.
                    try:
                        index_aniya = candidate_mothers.index("Aniya")
                    except ValueError:
                        continue
                    if abs(index_aniya - index_vshort) != 1:
                        continue
                    
                    # Clue 14: The person whose mother's name is Kailyn is in the third house (index 2).
                    if candidate_mothers[2] != "Kailyn":
                        continue
                    
                    # All constraints met; build solution.
                    solution_rows = []
                    for i in range(5):
                        # House numbers are 1-indexed.
                        row = [str(i+1), candidate_names[i], candidate_heights[i], candidate_mothers[i], candidate_hair[i]]
                        solution_rows.append(row)
                    
                    output = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Mother's name", "Hair color"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(output, indent=2))
                    return  # Exit after finding the first solution

if __name__ == "__main__":
    main()