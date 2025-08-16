import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]
    
    # Generate all possible permutations for the houses
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(mothers))
    
    # Filter permutations based on the clues
    valid_solutions = []
    for perm in all_permutations:
        name_perm, birthday_perm, mother_perm = perm[:2], perm[2:4], perm[4:]
        
        # Unpack the permutations for clarity
        name_house1, name_house2 = name_perm
        birthday_house1, birthday_house2 = birthday_perm
        mother_house1, mother_house2 = mother_perm
        
        # Apply the clues
        if (name_house1 == "Eric" or (name_house1 != "Eric" and name_house2 == "Eric" and mother_house1 == "Holly")) and \
           birthday_house1 == "april":
            valid_solutions.append((name_perm, birthday_perm, mother_perm))
    
    # Prepare the solution in the required format
    if valid_solutions:
        name_house1, name_house2 = valid_solutions[0][0]
        birthday_house1, birthday_house2 = valid_solutions[0][1]
        mother_house1, mother_house2 = valid_solutions[0][2]
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": [
                    ["1", name_house1, birthday_house1, mother_house1],
                    ["2", name_house2, birthday_house2, mother_house2]
                ]
            }
        }
        
        print(json.dumps(solution))

# Run the function to solve the puzzle and print the solution
solve_puzzle()