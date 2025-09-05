import itertools
import json

def solve_zebra_puzzle():
    names = ["Eric", "Arnold", "Peter"]
    vacations = ["mountain", "city", "beach"]
    heights = ["very short", "average", "short"]
    flowers = ["carnations", "daffodils", "lilies"]
    hair_colors = ["brown", "black", "blonde"]
    educations = ["associate", "bachelor", "high school"]

    for names_perm in itertools.permutations(names):
        for vac_perm in itertools.permutations(vacations):
            # Clue 4: The person who loves beach vacations is in the first house.
            if vac_perm[0] != "beach":
                continue
            for height_perm in itertools.permutations(heights):
                # Clue 3: The person who is very short is not in the second house.
                if height_perm[1] == "very short":
                    continue
                for flower_perm in itertools.permutations(flowers):
                    for hair_perm in itertools.permutations(hair_colors):
                        # Clue 11: The person who loves beach vacations is the person who has brown hair.
                        # Since the first house has beach vacation, its hair must be brown.
                        if hair_perm[0] != "brown":
                            continue
                        # Clue 10: The person who has blonde hair is in the third house.
                        if hair_perm[2] != "blonde":
                            continue
                        for edu_perm in itertools.permutations(educations):
                            # Clue 5: The person with a high school diploma is in the third house.
                            if edu_perm[2] != "high school":
                                continue

                            valid = True

                            # Clue 1: Peter is the person who has an average height.
                            for i in range(3):
                                if names_perm[i] == "Peter" and height_perm[i] != "average":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 2: The person who loves a bouquet of daffodils is Arnold.
                            for i in range(3):
                                if flower_perm[i] == "daffodils" and names_perm[i] != "Arnold":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 6: The person who is short is somewhere to the right of the person who is very short.
                            pos_very_short = None
                            pos_short = None
                            for i in range(3):
                                if height_perm[i] == "very short":
                                    pos_very_short = i
                                if height_perm[i] == "short":
                                    pos_short = i
                            if pos_very_short is None or pos_short is None or pos_short <= pos_very_short:
                                continue

                            # Clue 7: The person who loves the bouquet of lilies is Eric.
                            for i in range(3):
                                if flower_perm[i] == "lilies" and names_perm[i] != "Eric":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
                            for i in range(3):
                                if flower_perm[i] == "lilies" and edu_perm[i] != "bachelor":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
                            try:
                                peter_index = names_perm.index("Peter")
                            except ValueError:
                                continue
                            city_index = None
                            for i in range(3):
                                if vac_perm[i] == "city":
                                    city_index = i
                            if city_index is None or city_index <= peter_index:
                                continue

                            # Clue 11 (again, to be sure): Any house that loves beach vacations must have brown hair.
                            for i in range(3):
                                if vac_perm[i] == "beach" and hair_perm[i] != "brown":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # All constraints have been satisfied, so prepare the solution.
                            houses = []
                            for i in range(3):
                                row = [
                                    str(i + 1),
                                    names_perm[i],
                                    vac_perm[i],
                                    height_perm[i],
                                    flower_perm[i],
                                    hair_perm[i],
                                    edu_perm[i]
                                ]
                                houses.append(row)
                            
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                                    "rows": houses
                                }
                            }
                            print(json.dumps(result, indent=2))
                            return

if __name__ == "__main__":
    solve_zebra_puzzle()