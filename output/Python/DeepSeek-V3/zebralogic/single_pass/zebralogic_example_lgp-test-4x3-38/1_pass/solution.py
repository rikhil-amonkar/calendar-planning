import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
    flowers = ['carnations', 'roses', 'lilies', 'daffodils']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for flower_perm in permutations(flowers):
                # Assign each permutation to houses 1-4
                assignment = []
                for i in range(4):
                    assignment.append({
                        'House': houses[i],
                        'Name': name_perm[i],
                        'Mother': mother_perm[i],
                        'Flower': flower_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Constraint 8: Alice is in the third house
                if assignment[2]['Name'] != 'Alice':
                    valid = False
                    continue
                
                # Constraint 1: Alice's mother is Kailyn
                if assignment[2]['Mother'] != 'Kailyn':
                    valid = False
                    continue
                
                # Constraint 5: Arnold's mother is Holly
                arnold_house = None
                for house in assignment:
                    if house['Name'] == 'Arnold':
                        arnold_house = house
                        break
                if arnold_house is None or arnold_house['Mother'] != 'Holly':
                    valid = False
                    continue
                
                # Constraint 6: Carnations is right of Arnold's mother (Holly)
                carnation_house = None
                for house in assignment:
                    if house['Flower'] == 'carnations':
                        carnation_house = house
                        break
                if carnation_house is None or int(carnation_house['House']) <= int(arnold_house['House']):
                    valid = False
                    continue
                
                # Constraint 3: Peter is right of carnations
                peter_house = None
                for house in assignment:
                    if house['Name'] == 'Peter':
                        peter_house = house
                        break
                if peter_house is None or int(peter_house['House']) <= int(carnation_house['House']):
                    valid = False
                    continue
                
                # Constraint 4: Eric loves daffodils
                for house in assignment:
                    if house['Name'] == 'Eric' and house['Flower'] != 'daffodils':
                        valid = False
                        break
                if not valid:
                    continue
                
                # Constraint 2: Janelle is right of Arnold
                janelle_house = None
                for house in assignment:
                    if house['Mother'] == 'Janelle':
                        janelle_house = house
                        break
                if janelle_house is None or int(janelle_house['House']) <= int(arnold_house['House']):
                    valid = False
                    continue
                
                # Constraint 7: Lilies is directly left of Alice (house 3)
                if assignment[1]['Flower'] != 'lilies':
                    valid = False
                    continue
                
                if valid:
                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Flower"],
                            "rows": []
                        }
                    }
                    for house in assignment:
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Mother'],
                            house['Flower']
                        ])
                    return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())