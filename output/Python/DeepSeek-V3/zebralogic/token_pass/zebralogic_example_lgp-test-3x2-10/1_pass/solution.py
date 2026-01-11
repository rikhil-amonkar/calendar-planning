import json
from itertools import permutations

def solve_puzzle():
    # Define possible values
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]
    houses = [1, 2, 3]
    
    # Generate all possible permutations of names and heights
    all_name_perms = list(permutations(names, 3))
    all_height_perms = list(permutations(heights, 3))
    
    solutions = []
    
    # Try all combinations
    for name_perm in all_name_perms:
        for height_perm in all_height_perms:
            # Create assignment: house i gets name_perm[i-1] and height_perm[i-1]
            assignment = {}
            for i in range(3):
                house = i + 1
                assignment[house] = {
                    'name': name_perm[i],
                    'height': height_perm[i]
                }
            
            # Check clue 1: Eric is not in the first house
            if assignment[1]['name'] == 'Eric':
                continue
            
            # Check clue 2: very short is somewhere to the left of short
            # Find house numbers for these heights
            very_short_house = None
            short_house = None
            for house in houses:
                if assignment[house]['height'] == 'very short':
                    very_short_house = house
                if assignment[house]['height'] == 'short':
                    short_house = house
            
            if very_short_house is None or short_house is None:
                continue
            if not (very_short_house < short_house):
                continue
            
            # Check clue 3: The person who is very short is Eric
            for house in houses:
                if assignment[house]['height'] == 'very short' and assignment[house]['name'] != 'Eric':
                    break
            else:
                # Check clue 4: Arnold is not in the first house
                if assignment[1]['name'] == 'Arnold':
                    continue
                
                # All clues satisfied
                solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        solution = solutions[0]  # Should be unique
        rows = []
        for house in sorted(solution.keys()):
            rows.append([
                str(house),
                solution[house]['name'],
                solution[house]['height']
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())