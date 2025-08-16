#!/usr/bin/env python3
import itertools
import json

def main():
    # Define all attribute options
    names_list = ["Peter", "Arnold", "Eric", "Alice"]
    flowers_list = ["daffodils", "carnations", "roses", "lilies"]
    heights_list = ["very short", "short", "tall", "average"]
    mothers_list = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations_list = ["engineer", "doctor", "teacher", "artist"]
    sports_list = ["swimming", "basketball", "tennis", "soccer"]

    # There are 4 houses (indices 0..3 representing houses 1..4)
    # We'll try all combinations (permutations) and check all constraints.
    for names in itertools.permutations(names_list):
        # Iterate over occupations. Constraint: House1 must be teacher,
        # and the house with "Peter" must have "doctor".
        for occ in itertools.permutations(occupations_list):
            if occ[0] != "teacher":
                continue
            valid_occ = True
            for i in range(4):
                if names[i] == "Peter" and occ[i] != "doctor":
                    valid_occ = False
                    break
            if not valid_occ:
                continue

            for heights in itertools.permutations(heights_list):
                # Iterate over sports. Clues:
                # - The person who loves basketball has average height (and vice versa).
                # - The person who loves soccer is short (and vice versa).
                for sports in itertools.permutations(sports_list):
                    valid_sports = True
                    for i in range(4):
                        # Check basketball <-> average
                        if sports[i] == "basketball" and heights[i] != "average":
                            valid_sports = False
                            break
                        if heights[i] == "average" and sports[i] != "basketball":
                            valid_sports = False
                            break
                        # Check soccer <-> short
                        if sports[i] == "soccer" and heights[i] != "short":
                            valid_sports = False
                            break
                        if heights[i] == "short" and sports[i] != "soccer":
                            valid_sports = False
                            break
                    if not valid_sports:
                        continue

                    for flowers in itertools.permutations(flowers_list):
                        # Clues from flowers and names:
                        # - The person who loves roses is Eric.
                        # - The person who loves lilies is Arnold.
                        valid_flowers = True
                        for i in range(4):
                            if names[i] == "Eric" and flowers[i] != "roses":
                                valid_flowers = False
                                break
                            if names[i] == "Arnold" and flowers[i] != "lilies":
                                valid_flowers = False
                                break
                        if not valid_flowers:
                            continue
                        # Also, swimming must go with roses (and vice versa).
                        for i in range(4):
                            if sports[i] == "swimming" and flowers[i] != "roses":
                                valid_flowers = False
                                break
                            if flowers[i] == "roses" and sports[i] != "swimming":
                                valid_flowers = False
                                break
                        if not valid_flowers:
                            continue

                        for mothers in itertools.permutations(mothers_list):
                            # Clue: The person whose mother's name is Aniya is Alice.
                            valid_mothers = True
                            for i in range(4):
                                if names[i] == "Alice" and mothers[i] != "Aniya":
                                    valid_mothers = False
                                    break
                            if not valid_mothers:
                                continue
                            # Clue: The person whose mother's name is Janelle is the one who loves carnations.
                            for i in range(4):
                                if flowers[i] == "carnations" and mothers[i] != "Janelle":
                                    valid_mothers = False
                                    break
                                if mothers[i] == "Janelle" and flowers[i] != "carnations":
                                    valid_mothers = False
                                    break
                            if not valid_mothers:
                                continue

                            # Relative order constraints:
                            # Constraint 4: The person who loves daffodils is somewhere to the right of the engineer.
                            try:
                                index_engineer = occ.index("engineer")
                                index_daffodils = flowers.index("daffodils")
                            except ValueError:
                                continue
                            if index_engineer >= index_daffodils:
                                continue

                            # Constraint 10: The person whose mother's name is Holly is somewhere to the right of the person with average height.
                            try:
                                index_average = heights.index("average")
                                index_holly = mothers.index("Holly")
                            except ValueError:
                                continue
                            if index_average >= index_holly:
                                continue

                            # Other individual constraints:
                            # Clue 3: Arnold is tall.
                            valid_individual = True
                            for i in range(4):
                                if names[i] == "Arnold" and heights[i] != "tall":
                                    valid_individual = False
                                    break
                            if not valid_individual:
                                continue

                            # Constraint 9: Arnold is not in the third house (index 2).
                            for i in range(4):
                                if names[i] == "Arnold" and i == 2:
                                    valid_individual = False
                                    break
                            if not valid_individual:
                                continue

                            # At this point, check that every constraint has been satisfied:
                            # Clue 1 and 2 are satisfied by the roses/swimming/{"Eric"} combination.
                            # Clue 5 and 8 have been enforced by the sports-heights pairing.
                            # Clue 6 (teacher in house 1) and 11 (Peter is doctor) are already enforced.
                            # Clue 12 (Alice's mother is Aniya) is enforced.
                            # Clue 13 (Arnold loves lilies) is enforced.
                            # All constraints hold so we can build a solution.
                            solution_rows = []
                            for i in range(4):
                                # House numbers are 1-indexed as strings.
                                row = [str(i+1), names[i], flowers[i], heights[i], mothers[i], occ[i], sports[i]]
                                solution_rows.append(row)
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                    "rows": solution_rows
                                }
                            }
                            print(json.dumps(output))
                            return

if __name__ == "__main__":
    main()