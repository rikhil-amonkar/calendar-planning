import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for names and styles
    for name_perm in permutations(names):
        for style_perm in permutations(styles):
            solution = {
                '1': {'name': None, 'style': None},
                '2': {'name': None, 'style': None},
                '3': {'name': None, 'style': None},
                '4': {'name': None, 'style': None}
            }
            
            # Assign names and styles to houses
            for i in range(4):
                solution[houses[i]]['name'] = name_perm[i]
                solution[houses[i]]['style'] = style_perm[i]
            
            # Check constraints
            # Constraint 1: Alice is in the second house
            if solution['2']['name'] != 'Alice':
                continue
            
            # Constraint 5: The person in a Craftsman-style house is Alice
            if solution['2']['style'] != 'craftsman':
                # Wait, the style is 'craftsman' not 'craftsman'? Assuming typo in the clue
                if solution['2']['style'] != 'craftsman':
                    continue
            
            # Constraint 2: The person residing in a Victorian house is directly left of Peter
            peter_house = None
            victorian_house = None
            for house in houses:
                if solution[house]['name'] == 'Peter':
                    peter_house = house
                if solution[house]['style'] == 'victorian':
                    victorian_house = house
            if peter_house is None or victorian_house is None:
                continue
            if int(victorian_house) != int(peter_house) - 1:
                continue
            
            # Constraint 3: Peter is somewhere to the right of the person in a ranch-style home
            ranch_house = None
            for house in houses:
                if solution[house]['style'] == 'ranch':
                    ranch_house = house
                    break
            if ranch_house is None or int(ranch_house) >= int(peter_house):
                continue
            
            # Constraint 4: Arnold is somewhere to the right of the person in a Craftsman-style house
            craftsman_house = None
            arnold_house = None
            for house in houses:
                if solution[house]['style'] == 'craftsman':
                    craftsman_house = house
                if solution[house]['name'] == 'Arnold':
                    arnold_house = house
            if craftsman_house is None or arnold_house is None:
                continue
            if int(arnold_house) <= int(craftsman_house):
                continue
            
            # If all constraints are satisfied, format the solution
            formatted_solution = {
                "solution": {
                    "header": ["House", "Name", "style"],
                    "rows": []
                }
            }
            for house in houses:
                row = [house, solution[house]['name'], solution[house]['style']]
                formatted_solution["solution"]["rows"].append(row)
            return formatted_solution
    
    return {"solution": {"header": ["House", "Name", "style"], "rows": []}}

# Solve the puzzle and print the result
solution = solve_puzzle()
print(json.dumps(solution, indent=2))