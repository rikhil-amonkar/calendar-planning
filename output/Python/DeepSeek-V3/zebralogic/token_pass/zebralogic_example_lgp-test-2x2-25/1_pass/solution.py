import itertools
import json

def solve_puzzle():
    # Define all possible values
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]
    
    # Generate all possible permutations
    all_solutions = []
    
    # Generate all possible name assignments (bijection between houses and names)
    for name_perm in itertools.permutations(names, len(houses)):
        # Generate all possible vacation assignments
        for vac_perm in itertools.permutations(vacations, len(houses)):
            # Create assignment dictionary
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    "Name": name_perm[i],
                    "Vacation": vac_perm[i]
                }
            
            # Check clue 1: Arnold is somewhere to the right of the person who loves beach vacations
            # Find Arnold's house
            arnold_house = None
            beach_house = None
            
            for house in houses:
                if assignment[house]["Name"] == "Arnold":
                    arnold_house = house
                if assignment[house]["Vacation"] == "beach":
                    beach_house = house
            
            # Check if Arnold is to the right of beach person (higher house number)
            if arnold_house is not None and beach_house is not None:
                if arnold_house > beach_house:
                    all_solutions.append(assignment)
    
    # Format the solution
    if all_solutions:
        # Take the first valid solution (there should be only one for this puzzle)
        solution = all_solutions[0]
        
        # Build rows in house order
        rows = []
        for house in sorted(solution.keys()):
            rows.append([
                str(house),
                solution[house]["Name"],
                solution[house]["Vacation"]
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())