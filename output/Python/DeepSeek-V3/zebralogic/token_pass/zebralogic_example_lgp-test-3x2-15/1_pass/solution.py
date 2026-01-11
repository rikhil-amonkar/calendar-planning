import json
from itertools import permutations

def solve_puzzle():
    # Define possible values
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]
    houses = [1, 2, 3]
    
    # Generate all possible permutations of names and heights
    all_name_perms = list(permutations(names, 3))
    all_height_perms = list(permutations(heights, 3))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_perm in all_name_perms:
        for height_perm in all_height_perms:
            # Create assignment: house i -> (name, height)
            assignment = {}
            for i in range(3):
                assignment[i+1] = (name_perm[i], height_perm[i])
            
            # Check clue 1: Peter is somewhere to the right of Eric
            peter_house = None
            eric_house = None
            for house, (name, _) in assignment.items():
                if name == "Peter":
                    peter_house = house
                elif name == "Eric":
                    eric_house = house
            
            if peter_house is None or eric_house is None:
                continue
            if not peter_house > eric_house:
                continue
            
            # Check clue 2: The person who is short is in the first house
            if assignment[1][1] != "short":
                continue
            
            # Check clue 3: One house between short and very short
            short_house = None
            very_short_house = None
            for house, (_, height) in assignment.items():
                if height == "short":
                    short_house = house
                elif height == "very short":
                    very_short_house = house
            
            if short_house is None or very_short_house is None:
                continue
            if abs(short_house - very_short_house) != 2:
                continue
            
            # Check clue 4: Arnold and the person who is very short are next to each other
            arnold_house = None
            for house, (name, _) in assignment.items():
                if name == "Arnold":
                    arnold_house = house
                    break
            
            if arnold_house is None:
                continue
            if abs(arnold_house - very_short_house) != 1:
                continue
            
            # All clues satisfied, add to solutions
            solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        solution = solutions[0]  # Should be exactly one solution
        rows = []
        for house in sorted(solution.keys()):
            name, height = solution[house]
            rows.append([str(house), name, height])
        
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