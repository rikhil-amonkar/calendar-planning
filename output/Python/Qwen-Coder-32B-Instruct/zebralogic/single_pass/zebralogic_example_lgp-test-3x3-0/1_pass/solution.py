import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(educations)) * \
                       list(itertools.permutations(occupations))

    # Iterate through all possible combinations
    for names_perm, educations_perm, occupations_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(educations),
            itertools.permutations(occupations)
    ):
        # Unpack the permutations
        name1, name2, name3 = names_perm
        edu1, edu2, edu3 = educations_perm
        occ1, occ2, occ3 = occupations_perm

        # Check the clues
        if (occ1 == "teacher" and edu2 == "associate" and
            abs(names_perm.index("Eric") - educations_perm.index("associate")) == 1 and
            name1 == "Peter" and edu1 == "high school" and
            occ2 == "doctor" and edu2 == "bachelor"):
            # Construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Education", "Occupation"],
                    "rows": [
                        ["1", name1, edu1, occ1],
                        ["2", name2, edu2, occ2],
                        ["3", name3, edu3, occ3]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())