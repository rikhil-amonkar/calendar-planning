import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(names))
    all_permutations += list(itertools.permutations(cigars))
    all_permutations += list(itertools.permutations(hobbies))
    all_permutations += list(itertools.permutations(educations))
    all_permutations += list(itertools.permutations(drinks))

    # Check all combinations
    for name_perm in all_permutations[:6]:
        for cigar_perm in all_permutations[6:12]:
            for hobby_perm in all_permutations[12:18]:
                for education_perm in all_permutations[18:24]:
                    for drink_perm in all_permutations[24:]:
                        # Unpack permutations
                        name1, name2, name3 = name_perm
                        cigar1, cigar2, cigar3 = cigar_perm
                        hobby1, hobby2, hobby3 = hobby_perm
                        education1, education2, education3 = education_perm
                        drink1, drink2, drink3 = drink_perm

                        # Apply constraints
                        if cigar2 == "pall mall" and name2 == "Peter":
                            if drink2 == "milk" and education3 == "high school":
                                if name1 == "Eric" and drink1 == "tea":
                                    if (name1 == "Arnold" and cigar2 == "prince") or (name2 == "Arnold" and cigar3 == "prince"):
                                        if (hobby1 == "gardening" or hobby2 == "gardening") and cigar3 == "prince":
                                            if drink2 == "milk" and education2 == "associate":
                                                if education1 == "bachelor" and hobby2 == "photography":
                                                    # Solution found
                                                    solution = {
                                                        "solution": {
                                                            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                                                            "rows": [
                                                                [str(houses[0]), name1, cigar1, hobby1, education1, drink1],
                                                                [str(houses[1]), name2, cigar2, hobby2, education2, drink2],
                                                                [str(houses[2]), name3, cigar3, hobby3, education3, drink3]
                                                            ]
                                                        }
                                                    }
                                                    print(json.dumps(solution, indent=2))
                                                    return

# Run the solver
solve_puzzle()