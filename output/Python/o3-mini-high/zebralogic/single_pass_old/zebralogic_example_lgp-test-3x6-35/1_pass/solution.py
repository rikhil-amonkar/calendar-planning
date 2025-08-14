#!/usr/bin/env python3
import json
import itertools
import sys

def main():
    houses = 3
    names = ("Eric", "Arnold", "Peter")
    vacations = ("mountain", "city", "beach")
    heights = ("very short", "average", "short")
    flowers = ("carnations", "daffodils", "lilies")
    hair_colors = ("brown", "black", "blonde")
    educations = ("associate", "bachelor", "high school")
    
    for name_perm in itertools.permutations(names):
        for vac_perm in itertools.permutations(vacations):
            # Clue 4: The person who loves beach vacations is in the first house.
            if vac_perm[0] != "beach":
                continue
            for height_perm in itertools.permutations(heights):
                # Clue 3: The person who is very short is not in the second house.
                if height_perm[1] == "very short":
                    continue
                for flower_perm in itertools.permutations(flowers):
                    # Clue 7: The person who loves the bouquet of lilies is Eric.
                    if flower_perm.index("lilies") != name_perm.index("Eric"):
                        continue
                    # Clue 2: The person who loves a bouquet of daffodils is Arnold.
                    if flower_perm.index("daffodils") != name_perm.index("Arnold"):
                        continue
                    for hair_perm in itertools.permutations(hair_colors):
                        # Clue 10: The person who has blonde hair is in the third house.
                        if hair_perm[2] != "blonde":
                            continue
                        # Clue 11: The person who loves beach vacations is the person who has brown hair.
                        if hair_perm[0] != "brown":
                            continue
                        for edu_perm in itertools.permutations(educations):
                            # Clue 5: The person with a high school diploma is in the third house.
                            if edu_perm[2] != "high school":
                                continue
                            # Clue 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
                            if edu_perm[flower_perm.index("lilies")] != "bachelor":
                                continue
                            # Clue 1: Peter is the person who has an average height.
                            if height_perm[name_perm.index("Peter")] != "average":
                                continue
                            # Clue 6: The person who is short is somewhere to the right of the person who is very short.
                            if height_perm.index("short") <= height_perm.index("very short"):
                                continue
                            # Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
                            if vac_perm.index("city") <= name_perm.index("Peter"):
                                continue
                            
                            # Construct the solution.
                            rows = []
                            for i in range(houses):
                                row = [
                                    str(i+1),
                                    name_perm[i],
                                    vac_perm[i],
                                    height_perm[i],
                                    flower_perm[i],
                                    hair_perm[i],
                                    edu_perm[i]
                                ]
                                rows.append(row)
                            
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "vacation", "height", "favorite flower", "hair color", "education"],
                                    "rows": rows
                                }
                            }
                            print(json.dumps(solution))
                            sys.exit(0)

if __name__ == "__main__":
    main()