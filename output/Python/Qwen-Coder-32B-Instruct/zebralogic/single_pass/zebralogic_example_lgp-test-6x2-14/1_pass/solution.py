import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    # Generate all possible permutations for the attributes
    all_permutations = list(itertools.permutations(names)) * list(itertools.permutations(cigars))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(houses):
        # Unpack the houses into separate lists
        names_order, cigars_order = zip(*houses)

        # Check each clue
        if names_order.index("Arnold") >= names_order.index(cigars_order.index("blends")):
            return False
        if cigars_order[4] != "blue master":
            return False
        if names_order.index("Arnold") >= names_order.index(cigars_order.index("prince")):
            return False
        yellow_monster_index = cigars_order.index("yellow monster")
        blends_index = cigars_order.index("blends")
        if abs(yellow_monster_index - blends_index) != 2:
            return False
        if cigars_order[2] != "pall mall":
            return False
        if names_order[5] != "Eric":
            return False
        if abs(names_order.index("Carol") - names_order.index("Eric")) != 1:
            return False
        if names_order[0] != "Peter":
            return False
        if names_order[2] != "Bob":
            return False

        return True

    # Iterate through all permutations to find the valid solution
    for permutation in all_permutations:
        houses = list(zip(permutation[:6], permutation[6:]))
        if is_valid_solution(houses):
            break

    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": []
        }
    }

    for i, (name, cigar) in enumerate(houses, start=1):
        solution["solution"]["rows"].append([str(i), name, cigar])

    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

solve_puzzle()