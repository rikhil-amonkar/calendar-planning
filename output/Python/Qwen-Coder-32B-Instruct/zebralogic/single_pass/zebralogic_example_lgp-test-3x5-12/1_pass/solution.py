import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(cigars)) + \
                       list(itertools.permutations(hobbies)) + \
                       list(itertools.permutations(educations)) + \
                       list(itertools.permutations(drinks))

    # Check each combination of permutations to see if it satisfies all clues
    for names_perm in all_permutations[0:6]:
        for cigars_perm in all_permutations[6:12]:
            for hobbies_perm in all_permutations[12:18]:
                for educations_perm in all_permutations[18:24]:
                    for drinks_perm in all_permutations[24:30]:
                        # Unpack the current permutation
                        house1_name, house2_name, house3_name = names_perm
                        house1_cigar, house2_cigar, house3_cigar = cigars_perm
                        house1_hobby, house2_hobby, house3_hobby = hobbies_perm
                        house1_education, house2_education, house3_education = educations_perm
                        house1_drink, house2_drink, house3_drink = drinks_perm

                        # Check clue 1: The person partial to Pall Mall is Peter.
                        if house1_cigar == "pall mall" and house1_name != "Peter":
                            continue
                        if house2_cigar == "pall mall" and house2_name != "Peter":
                            continue
                        if house3_cigar == "pall mall" and house3_name != "Peter":
                            continue

                        # Check clue 2: The person who likes milk is directly left of the person with a high school diploma.
                        if house1_drink == "milk" and house2_education == "high school":
                            pass
                        elif house2_drink == "milk" and house3_education == "high school":
                            pass
                        else:
                            continue

                        # Check clue 3: Eric is the tea drinker.
                        if house1_name == "Eric" and house1_drink != "tea":
                            continue
                        if house2_name == "Eric" and house2_drink != "tea":
                            continue
                        if house3_name == "Eric" and house3_drink != "tea":
                            continue

                        # Check clue 4: Arnold and the Prince smoker are next to each other.
                        if (house1_name == "Arnold" and house2_cigar == "prince") or \
                           (house2_name == "Arnold" and house1_cigar == "prince") or \
                           (house2_name == "Arnold" and house3_cigar == "prince") or \
                           (house3_name == "Arnold" and house2_cigar == "prince"):
                            pass
                        else:
                            continue

                        # Check clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
                        if (house1_hobby == "gardening" and (house2_cigar == "prince" or house3_cigar == "prince")) or \
                           (house2_hobby == "gardening" and house3_cigar == "prince"):
                            pass
                        else:
                            continue

                        # Check clue 6: The person who likes milk is the person with an associate's degree.
                        if (house1_drink == "milk" and house1_education != "associate") or \
                           (house2_drink == "milk" and house2_education != "associate") or \
                           (house3_drink == "milk" and house3_education != "associate"):
                            continue

                        # Check clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
                        if (house1_education == "bachelor" and house2_hobby == "photography") or \
                           (house2_education == "bachelor" and house3_hobby == "photography"):
                            pass
                        else:
                            continue

                        # If all clues are satisfied, construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Favorite Cigar", "Hobby", "Education", "Favorite Drink"],
                                "rows": [
                                    ["1", house1_name, house1_cigar, house1_hobby, house1_education, house1_drink],
                                    ["2", house2_name, house2_cigar, house2_hobby, house2_education, house2_drink],
                                    ["3", house3_name, house3_cigar, house3_hobby, house3_education, house3_drink]
                                ]
                            }
                        }

                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
                        return

# Solve the puzzle
solve_puzzle()