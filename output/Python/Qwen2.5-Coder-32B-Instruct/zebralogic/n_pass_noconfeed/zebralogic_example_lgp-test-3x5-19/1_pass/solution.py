import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Peter", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    educations = ["associate", "high school", "bachelor"]
    smoothies = ["desert", "cherry", "watermelon"]
    hobbies = ["gardening", "cooking", "photography"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(occupations)) + \
                       list(itertools.permutations(educations)) + \
                       list(itertools.permutations(smoothies)) + \
                       list(itertools.permutations(hobbies))

    # Iterate over all possible combinations of permutations
    for names_perm in all_permutations[0:6]:
        for occupations_perm in all_permutations[6:12]:
            for educations_perm in all_permutations[12:18]:
                for smoothies_perm in all_permutations[18:24]:
                    for hobbies_perm in all_permutations[24:30]:
                        # Unpack the current permutation
                        name1, name2, name3 = names_perm
                        occupation1, occupation2, occupation3 = occupations_perm
                        education1, education2, education3 = educations_perm
                        smoothie1, smoothie2, smoothie3 = smoothies_perm
                        hobby1, hobby2, hobby3 = hobbies_perm

                        # Apply the clues to filter out invalid solutions
                        if (smoothie1 == "desert" and occupation1 != "doctor") or \
                           (smoothie2 == "desert" and occupation2 != "doctor") or \
                           (smoothie3 == "desert" and occupation3 != "doctor"):
                            continue
                        if name3 == "Arnold":
                            continue
                        if smoothies.index("cherry") < names.index("Peter"):
                            continue
                        if hobby2 != "cooking":
                            continue
                        if name2 != "Peter":
                            continue
                        if educations.index("associate") < hobbies.index("gardening"):
                            continue
                        if educations.index("bachelor") < smoothies.index("desert"):
                            continue
                        if occupation2 != "doctor":
                            continue
                        if occupation3 != "teacher":
                            continue
                        if hobby3 != "photography":
                            continue

                        # If all clues are satisfied, construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                                "rows": [
                                    ["1", name1, occupation1, education1, smoothie1, hobby1],
                                    ["2", name2, occupation2, education2, smoothie2, hobby2],
                                    ["3", name3, occupation3, education3, smoothie3, hobby3]
                                ]
                            }
                        }

                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
                        return

# Run the solver
solve_puzzle()