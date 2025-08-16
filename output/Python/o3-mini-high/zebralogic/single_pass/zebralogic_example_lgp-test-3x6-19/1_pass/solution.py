#!/usr/bin/env python3
import json
import itertools
import sys

def main():
    houses_count = 3

    names = ["Arnold", "Eric", "Peter"]
    cigars = ["pall mall", "blue master", "prince"]
    animals = ["horse", "cat", "bird"]
    children = ["Bella", "Fred", "Meredith"]
    bookGenres = ["science fiction", "romance", "mystery"]
    phoneModels = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            # Clue 3: the person with "pall mall" must be in the second house.
            if cigar_perm[1] != "pall mall":
                continue
            for animal_perm in itertools.permutations(animals):
                for child_perm in itertools.permutations(children):
                    for book_perm in itertools.permutations(bookGenres):
                        # Clue 11: The person who loves mystery books is not in the second house.
                        if book_perm[1] == "mystery":
                            continue
                        # Clue 10: The person who loves science fiction books is in the third house.
                        if book_perm[2] != "science fiction":
                            continue
                        for phone_perm in itertools.permutations(phoneModels):
                            # Build the list of houses (indexed 0,1,2 corresponds to houses 1,2,3)
                            houses_info = []
                            for i in range(houses_count):
                                houses_info.append({
                                    "House": str(i+1),
                                    "Name": name_perm[i],
                                    "Cigar": cigar_perm[i],
                                    "Animal": animal_perm[i],
                                    "Children": child_perm[i],
                                    "BookGenre": book_perm[i],
                                    "PhoneModel": phone_perm[i]
                                })

                            valid = True

                            # Clue 1: House with mystery book must have child Fred.
                            for house in houses_info:
                                if house["BookGenre"] == "mystery" and house["Children"] != "Fred":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 2: The cat lover is Eric.
                            for house in houses_info:
                                if house["Animal"] == "cat" and house["Name"] != "Eric":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 4: The person who keeps horses has child Meredith.
                            for house in houses_info:
                                if house["Animal"] == "horse" and house["Children"] != "Meredith":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 5: The person whose child is named Bella is the Prince smoker.
                            for house in houses_info:
                                if house["Children"] == "Bella" and house["Cigar"] != "prince":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 6: The person using an iPhone 13 is directly left of the person using a Samsung Galaxy S21.
                            found_adjacent_phone = False
                            for i in range(houses_count - 1):
                                if (houses_info[i]["PhoneModel"] == "iphone 13" and 
                                    houses_info[i+1]["PhoneModel"] == "samsung galaxy s21"):
                                    found_adjacent_phone = True
                                    break
                            if not found_adjacent_phone:
                                continue

                            # Clue 7: The person whose child is named Fred is directly left of Arnold.
                            found_adjacent_name = False
                            for i in range(houses_count - 1):
                                if houses_info[i]["Children"] == "Fred" and houses_info[i+1]["Name"] == "Arnold":
                                    found_adjacent_name = True
                                    break
                            if not found_adjacent_name:
                                continue

                            # Clue 8: Peter is somewhere to the left of Eric.
                            posPeter = None
                            posEric = None
                            for idx, house in enumerate(houses_info):
                                if house["Name"] == "Peter":
                                    posPeter = idx
                                if house["Name"] == "Eric":
                                    posEric = idx
                            if posPeter is None or posEric is None or posPeter >= posEric:
                                continue

                            # Clue 9: The person who loves science fiction books is the person using a Samsung Galaxy S21.
                            # Check both directions: if science fiction then phone must be samsung galaxy s21, and vice versa.
                            for house in houses_info:
                                if house["BookGenre"] == "science fiction" and house["PhoneModel"] != "samsung galaxy s21":
                                    valid = False
                                    break
                                if house["PhoneModel"] == "samsung galaxy s21" and house["BookGenre"] != "science fiction":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # All constraints satisfied; build solution dictionary.
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                                    "rows": []
                                }
                            }
                            for house in houses_info:
                                row = [house["House"], house["Name"], house["Cigar"], house["Animal"], house["Children"], house["BookGenre"], house["PhoneModel"]]
                                solution["solution"]["rows"].append(row)
                            
                            print(json.dumps(solution))
                            sys.exit(0)

if __name__ == "__main__":
    main()