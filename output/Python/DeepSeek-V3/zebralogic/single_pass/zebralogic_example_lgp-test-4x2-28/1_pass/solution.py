import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors = ['black', 'blonde', 'brown', 'red']
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for names and hair colors
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            # Assign to houses
            assignment = []
            for i in range(4):
                assignment.append({
                    'House': str(i + 1),
                    'Name': name_perm[i],
                    'hair': hair_perm[i]
                })
            
            # Check constraints
            # Constraint 5: Alice is in the first house
            if assignment[0]['Name'] != 'Alice':
                continue
            
            # Constraint 3: Eric has brown hair
            eric_house = None
            for house in assignment:
                if house['Name'] == 'Eric' and house['hair'] != 'brown':
                    break
            else:
                # Find Eric's house
                eric_house = None
                for house in assignment:
                    if house['Name'] == 'Eric':
                        eric_house = house
                        break
                if eric_house is None:
                    continue  # Eric must be present
                
                # Constraint 1: Eric is directly left of the person who has blonde hair
                eric_index = int(eric_house['House']) - 1
                if eric_index >= 3:
                    continue  # Eric cannot be in the last house
                if assignment[eric_index + 1]['hair'] != 'blonde':
                    continue
                
                # Constraint 2: Alice and Arnold are next to each other
                alice_index = 0  # since Alice is in first house
                arnold_index = None
                for i, house in enumerate(assignment):
                    if house['Name'] == 'Arnold':
                        arnold_index = i
                        break
                if arnold_index is None:
                    continue  # Arnold must be present
                if abs(alice_index - arnold_index) != 1:
                    continue
                
                # Constraint 4: The person who has black hair is not in the first house
                if assignment[0]['hair'] == 'black':
                    continue
                
                # All constraints satisfied, prepare the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "hair"],
                        "rows": []
                    }
                }
                for house in assignment:
                    solution["solution"]["rows"].append([
                        house['House'],
                        house['Name'],
                        house['hair']
                    ])
                return solution
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))