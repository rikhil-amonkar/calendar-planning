import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Peter", "Arnold"]
    mothers = ["Holly", "Aniya", "Janelle"]
    lunches = ["pizza", "grilled cheese", "spaghetti"]

    # Generate all possible permutations for each attribute
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(mothers)) * \
                   list(itertools.permutations(lunches))

    # Define the constraints
    def constraint1(house1, house2):
        return ("spaghetti" in house1 and "Peter" in house2) or \
               ("spaghetti" in house2 and "Peter" in house1)

    def constraint2(house1, house2):
        return "grilled cheese" in house1 and "Aniya" in house2

    def constraint3(house):
        return "grilled cheese" in house and "Eric" in house

    def constraint4(house):
        return "Peter" in house and "Holly" in house

    # Iterate over all possible combinations of permutations
    for names_perm, mothers_perm, lunches_perm in zip(permutations[::6], permutations[1::6], permutations[2::6]):
        houses = list(zip(names_perm, mothers_perm, lunches_perm))
        
        # Check constraints
        if (constraint1(houses[0], houses[1]) or constraint1(houses[1], houses[2])) and \
           constraint2(houses[0], houses[1]) and \
           constraint3(houses[0]) and \
           constraint4(houses[1]):
            # Format the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Lunch"],
                    "rows": [
                        ["1", houses[0][0], houses[0][1], houses[0][2]],
                        ["2", houses[1][0], houses[1][1], houses[1][2]],
                        ["3", houses[2][0], houses[2][1], houses[2][2]]
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()