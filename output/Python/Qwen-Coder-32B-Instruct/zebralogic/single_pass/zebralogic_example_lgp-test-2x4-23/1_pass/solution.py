import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    mothers_names = ["Aniya", "Holly"]
    car_models = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]

    # Generate all possible permutations for the attributes
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(mothers_names)) * \
                       list(itertools.permutations(car_models)) * \
                       list(itertools.permutations(heights))

    # Define the constraints
    def is_valid_solution(permutation):
        # Unpack the permutation into separate lists
        name_perm, mother_perm, car_perm, height_perm = (
            permutation[:2], permutation[2:4], permutation[4:6], permutation[6:]
        )

        # Constraint 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
        if car_perm.index("tesla model 3") < name_perm.index("Arnold"):
            return False

        # Constraint 2: Arnold is the person who is short.
        if name_perm[height_perm.index("short")] != "Arnold":
            return False

        # Constraint 3: The person whose mother's name is Holly is in the second house.
        if mother_perm[1] != "Holly":
            return False

        return True

    # Find the valid solution
    for permutation in all_permutations:
        if is_valid_solution(permutation):
            # Unpack the permutation into separate lists
            name_perm, mother_perm, car_perm, height_perm = (
                permutation[:2], permutation[2:4], permutation[4:6], permutation[6:]
            )
            # Prepare the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother's Name", "Car Model", "Height"],
                    "rows": [
                        ["1", name_perm[0], mother_perm[0], car_perm[0], height_perm[0]],
                        ["2", name_perm[1], mother_perm[1], car_perm[1], height_perm[1]]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Run the solver and print the solution
print(solve_puzzle())