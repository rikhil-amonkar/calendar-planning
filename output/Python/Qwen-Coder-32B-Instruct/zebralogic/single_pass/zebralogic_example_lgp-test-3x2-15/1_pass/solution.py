import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]
    
    # Generate all possible permutations for names and heights
    name_permutations = list(itertools.permutations(names))
    height_permutations = list(itertools.permutations(heights))
    
    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(name_order, height_order):
        # Unpack the permutations into individual variables for clarity
        name_house1, name_house2, name_house3 = name_order
        height_house1, height_house2, height_house3 = height_order
        
        # Check clue 1: Peter is somewhere to the right of Eric
        if name_order.index("Peter") < name_order.index("Eric"):
            return False
        
        # Check clue 2: The person who is short is in the first house
        if height_house1 != "short":
            return False
        
        # Check clue 3: There is one house between the person who is short and the person who is very short
        if abs(height_order.index("short") - height_order.index("very short")) != 2:
            return False
        
        # Check clue 4: Arnold and the person who is very short are next to each other
        if abs(name_order.index("Arnold") - height_order.index("very short")) != 1:
            return False
        
        return True
    
    # Iterate over all combinations of name and height permutations
    for name_order in name_permutations:
        for height_order in height_permutations:
            if is_valid_solution(name_order, height_order):
                # If a valid solution is found, construct the result
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [
                            ["1", name_order[0], height_order[0]],
                            ["2", name_order[1], height_order[1]],
                            ["3", name_order[2], height_order[2]]
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())