import json
from itertools import permutations

def solve_puzzle():
    # Define possible values for each attribute
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]
    
    houses = [1, 2]
    
    # Generate all possible permutations for each attribute across houses
    name_perms = list(permutations(names, 2))
    birthday_perms = list(permutations(birthdays, 2))
    color_perms = list(permutations(colors, 2))
    
    solutions = []
    
    # Brute-force search through all combinations
    for name_assign in name_perms:
        for birthday_assign in birthday_perms:
            for color_assign in color_perms:
                # Build assignment dictionaries
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'Name': name_assign[i],
                        'Birthday': birthday_assign[i],
                        'Color': color_assign[i]
                    }
                
                # Check clue 1: Eric loves yellow
                clue1_ok = True
                for house in houses:
                    if assignment[house]['Name'] == 'Eric' and assignment[house]['Color'] != 'yellow':
                        clue1_ok = False
                        break
                if not clue1_ok:
                    continue
                
                # Check clue 2: April birthday in house 1
                if assignment[1]['Birthday'] != 'april':
                    continue
                
                # Check clue 3: Yellow not in house 1
                if assignment[1]['Color'] == 'yellow':
                    continue
                
                # All clues satisfied
                solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        solution = solutions[0]  # Should be exactly one solution
        rows = []
        for house in sorted(solution.keys()):
            rows.append([
                str(house),
                solution[house]['Name'],
                solution[house]['Birthday'],
                solution[house]['Color']
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Color"],
                "rows": rows
            }
        }
        return result
    else:
        return {"solution": None}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))