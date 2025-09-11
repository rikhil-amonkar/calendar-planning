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
    for name_perm in itertools.permutations(names):
        for birthday_perm in itertools.permutations(birthdays):
            for mother_perm in itertools.permutations(mothers):
                # Unpack permutations
                name1, name2 = name_perm
                birthday1, birthday2 = birthday_perm
                mother1, mother2 = mother_perm
                
                # Check clue 1: Eric is somewhere to the left of The person whose mother's name is Holly.
                if name1 == "Eric" and mother2 == "Holly":
                    continue
                if name2 == "Eric" and mother1 == "Holly":
                    continue
                
                # Check clue 2: The person whose birthday is in April is in the first house.
                if birthday1 != "april":
                    continue
                
                # If all clues are satisfied, add to valid solutions
                valid_solutions.append({
                    "House": ["1", "2"],
                    "Name": [name1, name2],
                    "Birthday": [birthday1, birthday2],
                    "Mother": [mother1, mother2]
                })
    
    # Format the solution as required
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": [
                [valid_solutions[0]["House"][0], valid_solutions[0]["Name"][0], valid_solutions[0]["Birthday"][0], valid_solutions[0]["Mother"][0]],
                [valid_solutions[0]["House"][1], valid_solutions[0]["Name"][1], valid_solutions[0]["Birthday"][1], valid_solutions[0]["Mother"][1]]
            ]
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    solve_puzzle()