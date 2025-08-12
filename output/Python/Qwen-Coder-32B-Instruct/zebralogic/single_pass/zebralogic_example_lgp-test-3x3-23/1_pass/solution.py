import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    # Generate all possible permutations for the attributes
    all_permutations = list(itertools.permutations(names)) * list(itertools.permutations(occupations)) * list(itertools.permutations(hobbies))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(names_perm, occupations_perm, hobbies_perm):
        # Unpack the permutations into individual lists for each house
        name1, name2, name3 = names_perm
        occ1, occ2, occ3 = occupations_perm
        hob1, hob2, hob3 = hobbies_perm

        # Check clue 1: The person who is a doctor and Eric are next to each other.
        if (occ1 == "doctor" and name2 == "Eric") or (name1 == "Eric" and occ2 == "doctor"):
            pass
        elif (occ2 == "doctor" and name3 == "Eric") or (name2 == "Eric" and occ3 == "doctor"):
            pass
        else:
            return False

        # Check clue 2: The person who loves cooking is directly left of the person who is a teacher.
        if (hob1 == "cooking" and occ2 == "teacher") or (hob2 == "cooking" and occ3 == "teacher"):
            pass
        else:
            return False

        # Check clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
        if (hob1 == "gardening" and occ2 == "doctor") or (hob1 == "gardening" and occ3 == "doctor") or (hob2 == "gardening" and occ3 == "doctor"):
            pass
        else:
            return False

        # Check clue 4: The photography enthusiast is the person who is a teacher.
        if (hob1 == "photography" and occ1 == "teacher") or (hob2 == "photography" and occ2 == "teacher") or (hob3 == "photography" and occ3 == "teacher"):
            pass
        else:
            return False

        # Check clue 5: The person who is an engineer is Peter.
        if (occ1 == "engineer" and name1 == "Peter") or (occ2 == "engineer" and name2 == "Peter") or (occ3 == "engineer" and name3 == "Peter"):
            pass
        else:
            return False

        return True

    # Iterate over all possible combinations of permutations
    for names_perm in itertools.permutations(names):
        for occupations_perm in itertools.permutations(occupations):
            for hobbies_perm in itertools.permutations(hobbies):
                if is_valid_solution(names_perm, occupations_perm, hobbies_perm):
                    # If a valid solution is found, format it as required
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Occupation", "Hobby"],
                            "rows": [
                                ["1", names_perm[0], occupations_perm[0], hobbies_perm[0]],
                                ["2", names_perm[1], occupations_perm[1], hobbies_perm[1]],
                                ["3", names_perm[2], occupations_perm[2], hobbies_perm[2]]
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Run the function and print the result
print(solve_puzzle())