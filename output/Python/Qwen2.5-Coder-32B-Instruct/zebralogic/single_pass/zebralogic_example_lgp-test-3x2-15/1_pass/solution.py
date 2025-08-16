import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]
    
    # Generate all possible permutations for names and heights
    name_permutations = list(itertools.permutations(names))
    height_permutations = list(itertools.permutations(heights))
    
    # Iterate through all combinations of name and height permutations
    for name_order in name_permutations:
        for height_order in height_permutations:
            # Unpack the permutations into individual variables for easier reference
            name1, name2, name3 = name_order
            height1, height2, height3 = height_order
            
            # Check each clue to see if the current permutation satisfies all conditions
            if (name_order.index("Peter") > name_order.index("Eric") and  # Clue 1
                height1 == "short" and  # Clue 2
                abs(height_order.index("short") - height_order.index("very short")) == 2 and  # Clue 3
                abs(name_order.index("Arnold") - height_order.index("very short")) == 1):  # Clue 4
                
                # If all clues are satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [
                            ["1", name1, height1],
                            ["2", name2, height2],
                            ["3", name3, height3]
                        ]
                    }
                }
                
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return

# Run the function to solve the puzzle
solve_puzzle()