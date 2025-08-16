import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
    vacations = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']
    
    # Initialize possibilities
    solution = None
    
    # Generate all possible name and vacation permutations
    for name_perm in permutations(names):
        for vac_perm in permutations(vacations):
            # Create a dictionary to hold the current assignment
            assignment = {house: {'Name': None, 'Vacation': None} for house in houses}
            valid = True
            
            # Assign names and vacations to houses
            for i, house in enumerate(houses):
                assignment[house]['Name'] = name_perm[i]
                assignment[house]['Vacation'] = vac_perm[i]
            
            # Check constraints
            # Constraint 3: Eric is in the second house
            if assignment[2]['Name'] != 'Eric':
                valid = False
                continue
            
            # Constraint 2: Eric is somewhere to the right of Alice (Alice is left of Eric)
            alice_house = None
            eric_house = 2
            for house in houses:
                if assignment[house]['Name'] == 'Alice':
                    alice_house = house
                    break
            if alice_house is None or alice_house >= eric_house:
                valid = False
                continue
            
            # Constraint 4: cultural is in the third house
            if assignment[3]['Vacation'] != 'cultural':
                valid = False
                continue
            
            # Constraint 7: cultural is Peter
            if assignment[3]['Name'] != 'Peter':
                valid = False
                continue
            
            # Constraint 1: cultural is left of beach
            beach_house = None
            for house in houses:
                if assignment[house]['Vacation'] == 'beach':
                    beach_house = house
                    break
            if beach_house is None or beach_house <= 3:
                valid = False
                continue
            
            # Constraint 5: Bob is directly left of Arnold
            bob_house = None
            arnold_house = None
            for house in houses:
                if assignment[house]['Name'] == 'Bob':
                    bob_house = house
                if assignment[house]['Name'] == 'Arnold':
                    arnold_house = house
            if bob_house is None or arnold_house is None or arnold_house != bob_house + 1:
                valid = False
                continue
            
            # Constraint 8: cruise is Bob
            if assignment[bob_house]['Vacation'] != 'cruise':
                valid = False
                continue
            
            # Constraint 9: city is in the fourth house
            if assignment[4]['Vacation'] != 'city':
                valid = False
                continue
            
            # Constraint 6: camping is not in the first house
            if assignment[1]['Vacation'] == 'camping':
                valid = False
                continue
            
            # If all constraints are satisfied
            if valid:
                solution = assignment
                break
        if solution is not None:
            break
    
    # Format the solution as JSON
    if solution is not None:
        rows = []
        for house in houses:
            rows.append([
                str(house),
                solution[house]['Name'],
                solution[house]['Vacation']
            ])
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        return json.dumps(output, indent=2)
    else:
        return json.dumps({"solution": None})

print(solve_puzzle())