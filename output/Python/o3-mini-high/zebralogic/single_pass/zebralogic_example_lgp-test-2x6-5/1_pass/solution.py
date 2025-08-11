#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the possible values for each attribute
    names = ["Arnold", "Eric"]
    occupations = ["engineer", "doctor"]
    birthday_months = ["april", "sept"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    favorite_cigars = ["pall mall", "prince"]

    # Iterate over all possible assignments using permutations
    for names_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            # Clue 1: The engineer is in the first house.
            if occ_perm[0] != "engineer":
                continue
            for bmonth_perm in itertools.permutations(birthday_months):
                # Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
                # With two houses, they can only be neighbors if:
                # - House1 has birthday "april" and House2 is "doctor", OR
                # - House2 has birthday "april" and House1 is "doctor"
                # Since house1 is engineer (by clue 1) and cannot be doctor, the only possibility is:
                if bmonth_perm[0] == "april":
                    if occ_perm[1] != "doctor":
                        continue
                elif bmonth_perm[1] == "april":
                    if occ_perm[0] != "doctor":
                        continue
                else:
                    continue
                for style_perm in itertools.permutations(house_styles):
                    # Clue 3: The person living in a colonial-style house is the person who is an engineer.
                    # Find the index of "colonial" in style_perm, it must equal the engineer's index.
                    if style_perm.index("colonial") != occ_perm.index("engineer"):
                        continue
                    for height_perm in itertools.permutations(heights):
                        # Clue 4: The person who is very short is the person who is an engineer.
                        if height_perm.index("very short") != occ_perm.index("engineer"):
                            continue
                        for cigar_perm in itertools.permutations(favorite_cigars):
                            # Clue 5: The person who is short is the person partial to Pall Mall.
                            if height_perm.index("short") != cigar_perm.index("pall mall"):
                                continue
                            # Clue 6: The person who is an engineer is Eric.
                            if names_perm[occ_perm.index("engineer")] != "Eric":
                                continue

                            # If all constraints are satisfied, create house assignments.
                            house1 = {
                                "House": "1",
                                "Name": names_perm[0],
                                "Occupation": occ_perm[0],
                                "Birthday Month": bmonth_perm[0],
                                "House Style": style_perm[0],
                                "Height": height_perm[0],
                                "Favorite Cigar": cigar_perm[0]
                            }
                            house2 = {
                                "House": "2",
                                "Name": names_perm[1],
                                "Occupation": occ_perm[1],
                                "Birthday Month": bmonth_perm[1],
                                "House Style": style_perm[1],
                                "Height": height_perm[1],
                                "Favorite Cigar": cigar_perm[1]
                            }
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Occupation", "Birthday Month", "House Style", "Height", "Favorite Cigar"],
                                    "rows": [
                                        [house1["House"], house1["Name"], house1["Occupation"], house1["Birthday Month"], house1["House Style"], house1["Height"], house1["Favorite Cigar"]],
                                        [house2["House"], house2["Name"], house2["Occupation"], house2["Birthday Month"], house2["House Style"], house2["Height"], house2["Favorite Cigar"]]
                                    ]
                                }
                            }
                            print(json.dumps(solution))
                            return

if __name__ == "__main__":
    main()