import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Eric", "Arnold"]
    educations = ["bachelor", "associate", "high school"]
    occupations = ["teacher", "doctor", "engineer"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(educations)) * \
                       list(itertools.permutations(occupations))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(name_perm, education_perm, occupation_perm):
        # Unpack the permutations
        name1, name2, name3 = name_perm
        edu1, edu2, edu3 = education_perm
        occ1, occ2, occ3 = occupation_perm

        # Check each clue
        # Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
        if not ((occ1 == "teacher" and edu2 == "associate") or
                (occ2 == "teacher" and edu3 == "associate")):
            return False

        # Clue 2: The person with an associate's degree and Eric are next to each other.
        if not ((edu1 == "associate" and (name2 == "Eric" or name3 == "Eric")) or
                (edu2 == "associate" and (name1 == "Eric" or name3 == "Eric")) or
                (edu3 == "associate" and (name1 == "Eric" or name2 == "Eric"))):
            return False

        # Clue 3: Peter is the person with a high school diploma.
        if not (name1 == "Peter" and edu1 == "high school" or
                name2 == "Peter" and edu2 == "high school" or
                name3 == "Peter" and edu3 == "high school"):
            return False

        # Clue 4: The person who is a doctor is the person with a bachelor's degree.
        if not ((occ1 == "doctor" and edu1 == "bachelor") or
                (occ2 == "doctor" and edu2 == "bachelor") or
                (occ3 == "doctor" and edu3 == "bachelor")):
            return False

        return True

    # Iterate over all possible combinations of permutations
    for name_perm in itertools.permutations(names):
        for education_perm in itertools.permutations(educations):
            for occupation_perm in itertools.permutations(occupations):
                if is_valid_solution(name_perm, education_perm, occupation_perm):
                    # Construct the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Education", "Occupation"],
                            "rows": [
                                ["1", name_perm[0], education_perm[0], occupation_perm[0]],
                                ["2", name_perm[1], education_perm[1], occupation_perm[1]],
                                ["3", name_perm[2], education_perm[2], occupation_perm[2]]
                            ]
                        }
                    }
                    # Output the solution as JSON
                    print(json.dumps(solution))
                    return

# Run the solver
solve_puzzle()