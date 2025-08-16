#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Eric", "Arnold", "Peter"]
    vacations = ["mountain", "city", "beach"]
    heights = ["very short", "average", "short"]
    flowers = ["carnations", "daffodils", "lilies"]
    haircolors = ["brown", "black", "blonde"]
    educations = ["associate", "bachelor", "high school"]

    solution = None

    for nperm in itertools.permutations(names):
        for vperm in itertools.permutations(vacations):
            # Constraint 4: The person who loves beach vacations is in the first house.
            if vperm[0] != "beach":
                continue
            for hperm in itertools.permutations(heights):
                # Constraint 1: Peter is the person who has an average height.
                idx_peter = nperm.index("Peter")
                if hperm[idx_peter] != "average":
                    continue
                # Constraint 3: The person who is very short is not in the second house.
                if hperm[1] == "very short":
                    continue
                # Constraint 6: The person who is short is somewhere to the right of the person who is very short.
                idx_very_short = hperm.index("very short")
                idx_short = hperm.index("short")
                if idx_short <= idx_very_short:
                    continue
                for fperm in itertools.permutations(flowers):
                    # Constraint 2: The person who loves a bouquet of daffodils is Arnold.
                    valid = True
                    for i in range(3):
                        if fperm[i] == "daffodils" and nperm[i] != "Arnold":
                            valid = False
                            break
                        if nperm[i] == "Arnold" and fperm[i] != "daffodils":
                            valid = False
                            break
                    if not valid:
                        continue
                    # Constraint 7: The person who loves the bouquet of lilies is Eric.
                    valid = True
                    for i in range(3):
                        if fperm[i] == "lilies" and nperm[i] != "Eric":
                            valid = False
                            break
                        if nperm[i] == "Eric" and fperm[i] != "lilies":
                            valid = False
                            break
                    if not valid:
                        continue
                    for hcolperm in itertools.permutations(haircolors):
                        # Constraint 10: The person who has blonde hair is in the third house.
                        if hcolperm[2] != "blonde":
                            continue
                        # Constraint 11: The person who loves beach vacations is the person who has brown hair.
                        if hcolperm[0] != "brown":
                            continue
                        for eduperm in itertools.permutations(educations):
                            # Constraint 5: The person with a high school diploma is in the third house.
                            if eduperm[2] != "high school":
                                continue
                            # Constraint 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
                            valid = True
                            for i in range(3):
                                if fperm[i] == "lilies" and eduperm[i] != "bachelor":
                                    valid = False
                                    break
                                if eduperm[i] == "bachelor" and fperm[i] != "lilies":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            # Constraint 9: The person who prefers city breaks is somewhere to the right of Peter.
                            idx_city = vperm.index("city")
                            if idx_city <= nperm.index("Peter"):
                                continue

                            # All constraints satisfied, record the solution.
                            solution = []
                            for i in range(3):
                                solution.append([
                                    str(i + 1),
                                    nperm[i],
                                    vperm[i],
                                    hperm[i],
                                    fperm[i],
                                    hcolperm[i],
                                    eduperm[i]
                                ])
                            break
                        if solution:
                            break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()