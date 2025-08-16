import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]
    houses = [1, 2]

    # Generate all possible permutations for the assignments
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(foods)) * \
                       list(itertools.permutations(mothers))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(permutation):
        name_assignment = permutation[0]
        food_assignment = permutation[1]
        mother_assignment = permutation[2]

        # Unpack the assignments for easier reference
        name_house_1, name_house_2 = name_assignment
        food_house_1, food_house_2 = food_assignment
        mother_house_1, mother_house_2 = mother_assignment

        # Check clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
        if food_house_1 != "grilled cheese" or food_house_2 != "pizza":
            return False

        # Check clue 2: Arnold is not in the second house.
        if name_house_2 == "Arnold":
            return False

        # Check clue 3: Arnold is The person whose mother's name is Holly.
        if name_house_1 == "Arnold" and mother_house_1 != "Holly":
            return False
        if name_house_2 == "Arnold" and mother_house_2 != "Holly":
            return False

        return True

    # Find the valid solution
    for permutation in all_permutations:
        if is_valid_solution(permutation):
            name_assignment = permutation[0]
            food_assignment = permutation[1]
            mother_assignment = permutation[2]

            # Prepare the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Food", "Mother"],
                    "rows": [
                        [str(houses[0]), name_assignment[0], food_assignment[0], mother_assignment[0]],
                        [str(houses[1]), name_assignment[1], food_assignment[1], mother_assignment[1]]
                    ]
                }
            }

            # Output the solution as JSON
            print(json.dumps(solution))
            return

# Run the solver
solve_puzzle()