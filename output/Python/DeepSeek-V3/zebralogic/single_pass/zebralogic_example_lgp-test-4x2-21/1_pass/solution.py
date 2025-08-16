import json
from itertools import permutations

def solve_puzzle():
    # Define the domains
    houses = [1, 2, 3, 4]
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']

    # Generate all possible permutations for names and styles
    for name_perm in permutations(names):
        # Constraint 1: Alice is in the second house
        if name_perm[1] != 'Alice':
            continue

        for style_perm in permutations(styles):
            # Constraint 5: The person in a Craftsman-style house is Alice
            # Alice is in house 2, so house 2 must be craftsman
            if style_perm[1] != 'craftsman':
                continue

            # Constraint 4: Arnold is to the right of the person in a Craftsman-style house
            craftsman_house = style_perm.index('craftsman') + 1
            arnold_house = name_perm.index('Arnold') + 1
            if arnold_house <= craftsman_house:
                continue

            # Constraint 2: Victorian is directly left of Peter
            peter_house = name_perm.index('Peter') + 1
            if peter_house == 1:
                continue  # Victorian can't be left of house 1
            if style_perm[peter_house - 2] != 'victorian':
                continue

            # Constraint 3: Peter is to the right of ranch
            ranch_house = style_perm.index('ranch') + 1
            if peter_house <= ranch_house:
                continue

            # All constraints satisfied, build the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "HouseStyle"],
                    "rows": []
                }
            }
            for house in houses:
                solution["solution"]["rows"].append([
                    str(house),
                    name_perm[house - 1],
                    style_perm[house - 1]
                ])
            return solution

    return {"solution": {"header": ["House", "Name", "HouseStyle"], "rows": []}}

# Solve and output the puzzle
solution = solve_puzzle()
print(json.dumps(solution, indent=2))