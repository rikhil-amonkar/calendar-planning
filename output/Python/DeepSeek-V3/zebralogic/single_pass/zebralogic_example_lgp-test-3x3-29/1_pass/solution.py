import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    houses = ['1', '2', '3']
    names = ['Eric', 'Peter', 'Arnold']
    mothers = ['Holly', 'Aniya', 'Janelle']
    lunches = ['pizza', 'grilled cheese', 'spaghetti']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for lunch_perm in permutations(lunches):
                # Assign attributes to houses
                assignment = []
                for i in range(3):
                    assignment.append({
                        'House': houses[i],
                        'Name': name_perm[i],
                        'Mother': mother_perm[i],
                        'Lunch': lunch_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Constraint 1: spaghetti eater and Peter are next to each other
                peter_house = None
                spaghetti_house = None
                for house in assignment:
                    if house['Name'] == 'Peter':
                        peter_house = int(house['House'])
                    if house['Lunch'] == 'spaghetti':
                        spaghetti_house = int(house['House'])
                if abs(peter_house - spaghetti_house) != 1:
                    valid = False
                
                # Constraint 2: grilled cheese is directly left of Aniya's mother
                grilled_cheese_house = None
                aniya_house = None
                for house in assignment:
                    if house['Lunch'] == 'grilled cheese':
                        grilled_cheese_house = int(house['House'])
                    if house['Mother'] == 'Aniya':
                        aniya_house = int(house['House'])
                if grilled_cheese_house + 1 != aniya_house:
                    valid = False
                
                # Constraint 3: grilled cheese eater is Eric
                for house in assignment:
                    if house['Lunch'] == 'grilled cheese' and house['Name'] != 'Eric':
                        valid = False
                
                # Constraint 4: Peter's mother is Holly
                for house in assignment:
                    if house['Name'] == 'Peter' and house['Mother'] != 'Holly':
                        valid = False
                
                if valid:
                    # Prepare the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Lunch"],
                            "rows": []
                        }
                    }
                    for house in sorted(assignment, key=lambda x: x['House']):
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Mother'],
                            house['Lunch']
                        ])
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))