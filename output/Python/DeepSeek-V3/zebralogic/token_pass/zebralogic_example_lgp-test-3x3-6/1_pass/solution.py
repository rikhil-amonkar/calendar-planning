import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Eric", "Arnold", "Peter"]
    genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]
    
    houses = [1, 2, 3]
    
    # Generate all permutations for each category
    name_perms = list(permutations(names, 3))
    genre_perms = list(permutations(genres, 3))
    vacation_perms = list(permutations(vacations, 3))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_assignment in name_perms:
        # Clue 1: Eric is directly left of Arnold
        try:
            eric_index = name_assignment.index("Eric")
            arnold_index = name_assignment.index("Arnold")
            if arnold_index - eric_index != 1:
                continue
        except ValueError:
            continue
        
        for genre_assignment in genre_perms:
            for vacation_assignment in vacation_perms:
                # Build house assignments
                assignment = {}
                for i in range(3):
                    house = i + 1
                    assignment[house] = {
                        "Name": name_assignment[i],
                        "BookGenre": genre_assignment[i],
                        "Vacation": vacation_assignment[i]
                    }
                
                # Check all clues
                valid = True
                
                # Clue 2: Peter is somewhere to the right of the person who loves beach vacations
                beach_house = None
                peter_house = None
                for house in houses:
                    if assignment[house]["Vacation"] == "beach":
                        beach_house = house
                    if assignment[house]["Name"] == "Peter":
                        peter_house = house
                
                if beach_house is None or peter_house is None:
                    valid = False
                elif not peter_house > beach_house:
                    valid = False
                
                # Clue 3: Peter is the person who prefers city breaks
                if valid:
                    if assignment[peter_house]["Vacation"] != "city":
                        valid = False
                
                # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations
                if valid:
                    mystery_house = None
                    for house in houses:
                        if assignment[house]["BookGenre"] == "mystery":
                            mystery_house = house
                            break
                    
                    if mystery_house is None or not mystery_house < beach_house:
                        valid = False
                
                # Clue 5: The person who loves science fiction books is the person who loves beach vacations
                if valid:
                    for house in houses:
                        if assignment[house]["BookGenre"] == "science fiction":
                            if assignment[house]["Vacation"] != "beach":
                                valid = False
                            break
                
                if valid:
                    solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        solution = solutions[0]  # Should be unique
        rows = []
        for house in sorted(solution.keys()):
            row = [
                str(house),
                solution[house]["Name"],
                solution[house]["BookGenre"],
                solution[house]["Vacation"]
            ]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation"],
                "rows": rows
            }
        }
        return result
    else:
        return {"solution": None}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))