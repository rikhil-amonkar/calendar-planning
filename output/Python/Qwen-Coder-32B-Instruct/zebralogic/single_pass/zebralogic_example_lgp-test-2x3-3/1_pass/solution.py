import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Arnold", "Eric"]
    lunches = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]
    
    # Generate all possible permutations for the attributes
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(lunches)) * \
                       list(itertools.permutations(mothers))
    
    # Define the constraints
    def is_valid_solution(solution):
        # Unpack the solution
        (name1, name2), (lunch1, lunch2), (mother1, mother2) = solution
        
        # Constraint 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
        if lunch1 != "grilled cheese" or lunch2 != "pizza":
            return False
        
        # Constraint 2: Arnold is not in the second house.
        if name2 == "Arnold":
            return False
        
        # Constraint 3: Arnold is The person whose mother's name is Holly.
        if name1 == "Arnold" and mother1 != "Holly":
            return False
        if name2 == "Arnold" and mother2 != "Holly":
            return False
        
        return True
    
    # Find the valid solution
    for permutation in all_permutations:
        if is_valid_solution(permutation):
            (name1, name2), (lunch1, lunch2), (mother1, mother2) = permutation
            solution = {
                "solution": {
                    "header": ["House", "Name", "Lunch", "Mother"],
                    "rows": [
                        ["1", name1, lunch1, mother1],
                        ["2", name2, lunch2, mother2]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())