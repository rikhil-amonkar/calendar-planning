#!/usr/bin/env python3
import itertools
import json

def main():
    names_list = ["Peter", "Arnold", "Eric", "Alice"]
    flowers_list = ["daffodils", "carnations", "roses", "lilies"]
    heights_list = ["very short", "short", "tall", "average"]
    mothers_list = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations_list = ["engineer", "doctor", "teacher", "artist"]
    sports_list = ["swimming", "basketball", "tennis", "soccer"]

    # We represent houses as indices 0,1,2,3 (House number = index+1)
    for occ in itertools.permutations(occupations_list):
        # Clue 6: The teacher is in the first house.
        if occ[0] != "teacher":
            continue
        for names in itertools.permutations(names_list):
            valid = True
            for i in range(4):
                # Clue 11: Peter is the doctor.
                if names[i] == "Peter" and occ[i] != "doctor":
                    valid = False
                    break
                # Clue 9: Arnold is not in the third house.
                if i == 2 and names[i] == "Arnold":
                    valid = False
                    break
            if not valid:
                continue
            for flw in itertools.permutations(flowers_list):
                valid_flw = True
                for i in range(4):
                    # Clue 2: The person who loves the rose bouquet is Eric.
                    if names[i] == "Eric" and flw[i] != "roses":
                        valid_flw = False
                        break
                    # Clue 13: Arnold is the person who loves the bouquet of lilies.
                    if names[i] == "Arnold" and flw[i] != "lilies":
                        valid_flw = False
                        break
                if not valid_flw:
                    continue
                for sport in itertools.permutations(sports_list):
                    valid_sport = True
                    for i in range(4):
                        # Clue 1: The person who loves swimming is the person who loves the rose bouquet.
                        if sport[i] == "swimming" and flw[i] != "roses":
                            valid_sport = False
                            break
                        # Also Eric must love swimming (since he must have roses).
                        if names[i] == "Eric" and sport[i] != "swimming":
                            valid_sport = False
                            break
                    if not valid_sport:
                        continue
                    for height in itertools.permutations(heights_list):
                        valid_height = True
                        for i in range(4):
                            # Clue 3: Arnold is the person who is tall.
                            if names[i] == "Arnold" and height[i] != "tall":
                                valid_height = False
                                break
                            # Clue 8: The person who loves basketball is the person who has an average height.
                            if sport[i] == "basketball" and height[i] != "average":
                                valid_height = False
                                break
                            # Clue 5: The person who loves soccer is the person who is short.
                            if sport[i] == "soccer" and height[i] != "short":
                                valid_height = False
                                break
                        if not valid_height:
                            continue
                        for mom in itertools.permutations(mothers_list):
                            valid_mom = True
                            for i in range(4):
                                # Clue 7: The person whose mother's name is Janelle is the person who loves a carnations arrangement.
                                if mom[i] == "Janelle" and flw[i] != "carnations":
                                    valid_mom = False
                                    break
                                # Clue 12: The person whose mother's name is Aniya is Alice.
                                if mom[i] == "Aniya" and names[i] != "Alice":
                                    valid_mom = False
                                    break
                                if names[i] == "Alice" and mom[i] != "Aniya":
                                    valid_mom = False
                                    break
                            if not valid_mom:
                                continue
                            # Clue 10: The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
                            try:
                                index_avg = height.index("average")
                                index_holly = mom.index("Holly")
                                if index_holly <= index_avg:
                                    continue
                            except ValueError:
                                continue
                            # Clue 4: The person who loves a bouquet of daffodils is somewhere to the right of the person who is an engineer.
                            try:
                                index_engineer = occ.index("engineer")
                                index_daffodils = flw.index("daffodils")
                                if index_daffodils <= index_engineer:
                                    continue
                            except ValueError:
                                continue

                            # All constraints satisfied, build the solution.
                            header = ["House", "Name", "flower", "height", "mother", "occupation", "sport"]
                            rows = []
                            for i in range(4):
                                rows.append([str(i+1), names[i], flw[i], height[i], mom[i], occ[i], sport[i]])
                            result = {"solution": {"header": header, "rows": rows}}
                            print(json.dumps(result))
                            return

if __name__ == "__main__":
    main()