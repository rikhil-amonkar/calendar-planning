import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Arnold", "Peter", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    educations = ["associate", "high school", "bachelor"]
    smoothies = ["desert", "cherry", "watermelon"]
    hobbies = ["gardening", "cooking", "photography"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(occupations)) * \
                       list(itertools.permutations(educations)) * \
                       list(itertools.permutations(smoothies)) * \
                       list(itertools.permutations(hobbies))

    # Iterate through all possible combinations
    for names_perm, occupations_perm, educations_perm, smoothies_perm, hobbies_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(occupations),
            itertools.permutations(educations),
            itertools.permutations(smoothies),
            itertools.permutations(hobbies)
    ):
        # Unpack the permutations into more readable variables
        name1, name2, name3 = names_perm
        occupation1, occupation2, occupation3 = occupations_perm
        education1, education2, education3 = educations_perm
        smoothie1, smoothie2, smoothie3 = smoothies_perm
        hobby1, hobby2, hobby3 = hobbies_perm

        # Apply the clues
        if (smoothie1 == "desert" and occupation1 == "doctor") and \
           (name1 != "Arnold") and \
           (smoothie2 == "cherry" or smoothie3 == "cherry") and \
           (name2 == "Peter" and hobby2 == "cooking") and \
           (occupation2 == "doctor" and hobby2 == "cooking") and \
           (hobby1 == "gardening" and (education2 == "associate" or education3 == "associate")) and \
           (smoothie1 == "desert" and (education2 == "bachelor" or education3 == "bachelor")) and \
           (occupation2 == "teacher" and hobby2 == "photography"):
            # Construct the solution
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
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())