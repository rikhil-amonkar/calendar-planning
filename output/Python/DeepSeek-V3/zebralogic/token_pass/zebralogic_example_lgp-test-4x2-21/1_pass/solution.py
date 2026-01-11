import json
from itertools import permutations

def solve_puzzle():
    # Define possible values
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations of names and styles
    name_perms = list(permutations(names, 4))
    style_perms = list(permutations(styles, 4))
    
    solutions = []
    
    # Try all combinations
    for name_assignment in name_perms:
        for style_assignment in style_perms:
            # Create mapping for easy access
            assignment = {}
            for i in range(4):
                house = i + 1
                assignment[house] = {
                    'name': name_assignment[i],
                    'style': style_assignment[i]
                }
            
            # Check clue 1: Alice is in the second house
            if assignment[2]['name'] != 'Alice':
                continue
            
            # Check clue 5: The person in a Craftsman-style house is Alice
            # Find which house has craftsman style
            craftsman_house = None
            for house in houses:
                if assignment[house]['style'] == 'craftsman':
                    craftsman_house = house
                    break
            
            if craftsman_house is None or assignment[craftsman_house]['name'] != 'Alice':
                continue
            
            # Check clue 2: Victorian house is directly left of Peter
            # Find Victorian house and Peter's house
            victorian_house = None
            peter_house = None
            for house in houses:
                if assignment[house]['style'] == 'victorian':
                    victorian_house = house
                if assignment[house]['name'] == 'Peter':
                    peter_house = house
            
            if victorian_house is None or peter_house is None:
                continue
            
            if victorian_house + 1 != peter_house:
                continue
            
            # Check clue 3: Peter is somewhere to the right of the person in a ranch-style home
            ranch_house = None
            for house in houses:
                if assignment[house]['style'] == 'ranch':
                    ranch_house = house
                    break
            
            if ranch_house is None or peter_house <= ranch_house:
                continue
            
            # Check clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house
            arnold_house = None
            for house in houses:
                if assignment[house]['name'] == 'Arnold':
                    arnold_house = house
                    break
            
            if arnold_house is None or arnold_house <= craftsman_house:
                continue
            
            # All clues satisfied, add to solutions
            solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        solution = solutions[0]  # Should be exactly one solution
        rows = []
        for house in sorted(solution.keys()):
            rows.append([
                str(house),
                solution[house]['name'],
                solution[house]['style']
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())