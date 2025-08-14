#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]

    solution = None

    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for hobby_perm in itertools.permutations(hobbies):
                for edu_perm in itertools.permutations(educations):
                    for drink_perm in itertools.permutations(drinks):
                        # Build houses assignment for houses 1, 2, 3 (index 0, 1, 2)
                        houses = []
                        for i in range(3):
                            houses.append({
                                "House": str(i+1),
                                "Name": name_perm[i],
                                "favorite cigar": cigar_perm[i],
                                "hobby": hobby_perm[i],
                                "level of education": edu_perm[i],
                                "favorite drink": drink_perm[i]
                            })

                        valid = True

                        # Clue 1: The person partial to Pall Mall is Peter.
                        for i in range(3):
                            if cigar_perm[i] == "pall mall" and name_perm[i] != "Peter":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 2: The person who likes milk is directly left of the person with a high school diploma.
                        try:
                            milk_index = drink_perm.index("milk")
                        except ValueError:
                            continue
                        if milk_index == 2:
                            continue
                        if edu_perm[milk_index+1] != "high school":
                            continue

                        # Clue 3: Eric is the tea drinker.
                        try:
                            eric_index = name_perm.index("Eric")
                        except ValueError:
                            continue
                        if drink_perm[eric_index] != "tea":
                            continue

                        # Clue 4: Arnold and the Prince smoker are next to each other.
                        try:
                            arnold_index = name_perm.index("Arnold")
                        except ValueError:
                            continue
                        try:
                            prince_index = cigar_perm.index("prince")
                        except ValueError:
                            continue
                        if abs(arnold_index - prince_index) != 1:
                            continue

                        # Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
                        try:
                            gardening_index = hobby_perm.index("gardening")
                        except ValueError:
                            continue
                        if gardening_index >= prince_index:
                            continue

                        # Clue 6: The person who likes milk is the person with an associate's degree.
                        if edu_perm[milk_index] != "associate":
                            continue

                        # Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
                        try:
                            bachelor_index = edu_perm.index("bachelor")
                        except ValueError:
                            continue
                        if bachelor_index == 2:
                            continue
                        if hobby_perm[bachelor_index+1] != "photography":
                            continue

                        solution = houses
                        break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    return solution

def main():
    sol = solve_puzzle()
    header = ["House", "Name", "favorite cigar", "hobby", "level of education", "favorite drink"]
    rows = []
    if sol:
        for house in sol:
            rows.append([
                house["House"],
                house["Name"],
                house["favorite cigar"],
                house["hobby"],
                house["level of education"],
                house["favorite drink"]
            ])
    output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()