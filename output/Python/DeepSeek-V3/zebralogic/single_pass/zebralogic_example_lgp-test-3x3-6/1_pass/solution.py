import json
from itertools import permutations

def solve_puzzle():
    # Define possible values for each attribute
    names = ["Eric", "Arnold", "Peter"]
    genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]
    
    # Generate all possible permutations for each attribute
    for name_order in permutations(names):
        # Check clue 1: Eric is directly left of Arnold
        for i in range(2):
            if name_order[i] == "Eric" and name_order[i+1] == "Arnold":
                break
        else:
            continue
        
        for genre_order in permutations(genres):
            for vacation_order in permutations(vacations):
                # Check clue 3: Peter prefers city breaks
                if vacation_order[name_order.index("Peter")] != "city":
                    continue
                
                # Check clue 2: Peter is right of the person who loves beach vacations
                beach_pos = vacation_order.index("beach")
                peter_pos = name_order.index("Peter")
                if peter_pos <= beach_pos:
                    continue
                
                # Check clue 4: mystery is left of beach
                mystery_pos = genre_order.index("mystery")
                if mystery_pos >= beach_pos:
                    continue
                
                # Check clue 5: science fiction is beach
                if genre_order[vacation_order.index("beach")] != "science fiction":
                    continue
                
                # If all clues are satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Vacation"],
                        "rows": []
                    }
                }
                for house in range(1, 4):
                    idx = house - 1
                    solution["solution"]["rows"].append([
                        str(house),
                        name_order[idx],
                        genre_order[idx],
                        vacation_order[idx]
                    ])
                return solution
    
    return {"solution": {"header": ["House", "Name", "BookGenre", "Vacation"], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))