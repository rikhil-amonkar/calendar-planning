import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
    flowers = ['carnations', 'roses', 'lilies', 'daffodils']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for flower_perm in permutations(flowers):
                # Assign each permutation to houses
                assignment = []
                for i in range(4):
                    assignment.append({
                        'House': str(i+1),
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
                if not arnold_house or arnold_house['Mother'] != 'Holly':
                    valid = False
                    continue
                
                # Constraint 6: carnations is right of Holly (Arnold's house)
                carnation_house = None
                for house in assignment:
                    if house['Flower'] == 'carnations':
                        carnation_house = house
                        break
                if not carnation_house or int(carnation_house['House']) <= int(arnold_house['House']):
                    valid = False
                    continue
                
                # Constraint 3: Peter is right of carnations
                peter_house = None
                for house in assignment:
                    if house['Name'] == 'Peter':
                        peter_house = house
                        break
                if not peter_house or int(peter_house['House']) <= int(carnation_house['House']):
                    valid = False
                    continue
                
                # Constraint 4: Eric loves daffodils
                eric_house = None
                for house in assignment:
                    if house['Name'] == 'Eric':
                        eric_house = house
                        break
                if not eric_house or eric_house['Flower'] != 'daffodils':
                    valid = False
                    continue
                
                # Constraint 2: Janelle is right of Arnold
                janelle_house = None
                for house in assignment:
                    if house['Mother'] == 'Janelle':
                        janelle_house = house
                        break
                if not janelle_house or int(janelle_house['House']) <= int(arnold_house['House']):
                    valid = False
                    continue
                
                # Constraint 7: lilies is directly left of Alice (house 3)
                if assignment[1]['House'] != '2' or assignment[1]['Flower'] != 'lilies':
                    valid = False
                    continue
                
                if valid:
                    # Prepare the solution
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
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))