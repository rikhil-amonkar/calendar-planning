import itertools
import json

def main():
    names_list = ["Peter", "Arnold", "Eric", "Alice"]
    flowers_list = ["daffodils", "carnations", "roses", "lilies"]
    heights_list = ["very short", "short", "tall", "average"]
    mothers_list = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations_list = ["engineer", "doctor", "teacher", "artist"]
    sports_list = ["swimming", "basketball", "tennis", "soccer"]

    solution = None

    # Iterate over all possible assignments with early constraint checks.
    for names in itertools.permutations(names_list):
        # Clue 9: Arnold is not in the third house (index 2)
        if names[2] == "Arnold":
            continue

        for occupations in itertools.permutations(occupations_list):
            # Clue 6: The teacher is in the first house.
            if occupations[0] != "teacher":
                continue
            # Clue 11: Peter is the doctor.
            valid = True
            for i in range(4):
                if names[i] == "Peter" and occupations[i] != "doctor":
                    valid = False
                    break
            if not valid:
                continue

            for heights in itertools.permutations(heights_list):
                valid = True
                for i in range(4):
                    # Clue 3: Arnold is tall.
                    if names[i] == "Arnold" and heights[i] != "tall":
                        valid = False
                        break
                    # Deduction: Eric cannot be average (basketball) or short (soccer) or tall (Arnold’s) so must be very short.
                    if names[i] == "Eric" and heights[i] != "very short":
                        valid = False
                        break
                if not valid:
                    continue

                for flowers in itertools.permutations(flowers_list):
                    valid = True
                    for i in range(4):
                        # Clue 2: The person who loves the rose bouquet is Eric.
                        if names[i] == "Eric" and flowers[i] != "roses":
                            valid = False
                            break
                        # Clue 13: Arnold loves the bouquet of lilies.
                        if names[i] == "Arnold" and flowers[i] != "lilies":
                            valid = False
                            break
                    if not valid:
                        continue

                    for mothers in itertools.permutations(mothers_list):
                        valid = True
                        for i in range(4):
                            # Clue 12: The person whose mother's name is Aniya is Alice.
                            if names[i] == "Alice" and mothers[i] != "Aniya":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 7: The person whose mother's name is Janelle is the one with carnations.
                        for i in range(4):
                            if mothers[i] == "Janelle" and flowers[i] != "carnations":
                                valid = False
                                break
                            if flowers[i] == "carnations" and mothers[i] != "Janelle":
                                valid = False
                                break
                        if not valid:
                            continue

                        for sports in itertools.permutations(sports_list):
                            valid = True
                            for i in range(4):
                                # Clue 1: The person who loves swimming is the one with roses.
                                if sports[i] == "swimming" and flowers[i] != "roses":
                                    valid = False
                                    break
                                if flowers[i] == "roses" and sports[i] != "swimming":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            for i in range(4):
                                # Clue 5: The person who loves soccer is the person who is short.
                                if sports[i] == "soccer" and heights[i] != "short":
                                    valid = False
                                    break
                                if heights[i] == "short" and sports[i] != "soccer":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            for i in range(4):
                                # Clue 8: The person who loves basketball is the person who is average.
                                if sports[i] == "basketball" and heights[i] != "average":
                                    valid = False
                                    break
                                if heights[i] == "average" and sports[i] != "basketball":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 4: The house with daffodils is somewhere to the right of the house where the occupation is engineer.
                            try:
                                index_daffodils = flowers.index("daffodils")
                                index_engineer = occupations.index("engineer")
                            except ValueError:
                                valid = False
                            if not valid:
                                continue
                            if index_daffodils <= index_engineer:
                                continue
                            
                            # Clue 10: The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
                            try:
                                index_average = heights.index("average")
                                index_holly = mothers.index("Holly")
                            except ValueError:
                                valid = False
                            if not valid:
                                continue
                            if index_holly <= index_average:
                                continue
                            
                            # All constraints satisfied; capture the solution.
                            solution = {
                                "names": names,
                                "flowers": flowers,
                                "heights": heights,
                                "mothers": mothers,
                                "occupations": occupations,
                                "sports": sports
                            }
                            break
                        if solution is not None:
                            break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    if solution is None:
        result = {"solution": {"header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"], "rows": []}}
    else:
        # Build rows for houses 1 to 4 in order.
        rows = []
        for i in range(4):
            row = [
                str(i + 1),
                solution["names"][i],
                solution["flowers"][i],
                solution["heights"][i],
                solution["mothers"][i],
                solution["occupations"][i],
                solution["sports"][i]
            ]
            rows.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": rows
            }
        }
    print(json.dumps(result))

if __name__ == "__main__":
    main()