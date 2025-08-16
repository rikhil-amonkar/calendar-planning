#!/usr/bin/env python3
import json
import itertools

def solve():
    names = ["Arnold", "Eric"]
    occupations = ["engineer", "doctor"]
    birthdays = ["april", "sept"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    cigars = ["pall mall", "prince"]

    solution = None

    for name_perm in itertools.permutations(names):
        # Clue 6: The person who is an engineer is Eric.
        # Thus, the house with engineer (which is house 1 by Clue 1) must have name Eric.
        # So, name_perm[0] must be "Eric" if house1 is engineer.
        for occ_perm in itertools.permutations(occupations):
            # Clue 1: The person who is an engineer is in the first house.
            if occ_perm[0] != "engineer":
                continue
            if name_perm[0] != "Eric":
                continue

            for bday_perm in itertools.permutations(birthdays):
                # Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
                doctor_index = occ_perm.index("doctor")
                april_index = bday_perm.index("april")
                if abs(doctor_index - april_index) != 1:
                    continue

                for style_perm in itertools.permutations(house_styles):
                    # Clue 3: The person living in a colonial-style house is the person who is an engineer.
                    engineer_index = occ_perm.index("engineer")
                    if style_perm[engineer_index] != "colonial":
                        continue
                    valid_style = True
                    for i in range(2):
                        if style_perm[i] == "colonial" and occ_perm[i] != "engineer":
                            valid_style = False
                            break
                    if not valid_style:
                        continue

                    for height_perm in itertools.permutations(heights):
                        # Clue 4: The person who is very short is the person who is an engineer.
                        if height_perm[engineer_index] != "very short":
                            continue
                        valid_height = True
                        for i in range(2):
                            if height_perm[i] == "very short" and occ_perm[i] != "engineer":
                                valid_height = False
                                break
                        if not valid_height:
                            continue

                        for cigar_perm in itertools.permutations(cigars):
                            # Clue 5: The person who is short is the person partial to Pall Mall.
                            valid_cigar = True
                            for i in range(2):
                                if height_perm[i] == "short" and cigar_perm[i] != "pall mall":
                                    valid_cigar = False
                                    break
                            if not valid_cigar:
                                continue

                            houses_data = []
                            for i in range(2):
                                house_info = {
                                    "House": str(i+1),
                                    "Name": name_perm[i],
                                    "Occupation": occ_perm[i],
                                    "Birthday": bday_perm[i],
                                    "HouseStyle": style_perm[i],
                                    "Height": height_perm[i],
                                    "Cigar": cigar_perm[i]
                                }
                                houses_data.append(house_info)
                            solution = houses_data
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

    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"], "rows": []}}
    else:
        rows = []
        for house in solution:
            row = [
                house["House"],
                house["Name"],
                house["Occupation"],
                house["Birthday"],
                house["HouseStyle"],
                house["Height"],
                house["Cigar"]
            ]
            rows.append(row)
        output = {"solution": {"header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"], "rows": rows}}

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    solve()