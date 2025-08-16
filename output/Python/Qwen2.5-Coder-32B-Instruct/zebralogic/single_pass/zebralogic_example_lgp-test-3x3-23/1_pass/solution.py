import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(occupations)) * \
                   list(itertools.permutations(hobbies))

    # Define the constraints as functions
    def constraint1(houses):
        doctor_index = houses[1].index("doctor")
        eric_index = houses[0].index("Eric")
        return abs(doctor_index - eric_index) == 1

    def constraint2(houses):
        cooking_index = houses[2].index("cooking")
        teacher_index = houses[1].index("teacher")
        return cooking_index + 1 == teacher_index

    def constraint3(houses):
        doctor_index = houses[1].index("doctor")
        gardening_index = houses[2].index("gardening")
        return doctor_index > gardening_index

    def constraint4(houses):
        photography_index = houses[2].index("photography")
        teacher_index = houses[1].index("teacher")
        return photography_index == teacher_index

    def constraint5(houses):
        return houses[1][houses[0].index("Peter")] == "engineer"

    # Check each permutation to see if it satisfies all constraints
    for perm in permutations:
        names_perm, occupations_perm, hobbies_perm = perm[:3], perm[3:6], perm[6:]
        houses = [names_perm, occupations_perm, hobbies_perm]
        if (constraint1(houses) and constraint2(houses) and
            constraint3(houses) and constraint4(houses) and
            constraint5(houses)):
            # Construct the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Occupation", "Hobby"],
                    "rows": [
                        ["1", houses[0][0], houses[1][0], houses[2][0]],
                        ["2", houses[0][1], houses[1][1], houses[2][1]],
                        ["3", houses[0][2], houses[1][2], houses[2][2]]
                    ]
                }
            }
            print(json.dumps(solution))
            return

# Run the solver
solve_puzzle()