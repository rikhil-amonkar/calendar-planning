import json
from itertools import permutations

def solve_puzzle():
    # Define the categories and options
    houses = ['1', '2', '3']
    names = ['Eric', 'Peter', 'Arnold']
    mothers = ['Holly', 'Aniya', 'Janelle']
    foods = ['pizza', 'grilled cheese', 'spaghetti']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for food_perm in permutations(foods):
                # Assign each permutation to houses
                assignment = []
                for i in range(3):
                    assignment.append({
                        'House': houses[i],
                        'Name': name_perm[i],
                        'Mother': mother_perm[i],
                        'Food': food_perm[i]
                    })
                
                # Check all constraints
                # Constraint 3: The person who loves eating grilled cheese is Eric.
                grilled_cheese_eater = None
                for house in assignment:
                    if house['Food'] == 'grilled cheese':
                        grilled_cheese_eater = house['Name']
                if grilled_cheese_eater != 'Eric':
                    continue
                
                # Constraint 2: The person who loves eating grilled cheese is directly left of The person whose mother's name is Aniya.
                grilled_house_index = None
                aniya_mother_house_index = None
                for i in range(3):
                    if assignment[i]['Food'] == 'grilled cheese':
                        grilled_house_index = i
                    if assignment[i]['Mother'] == 'Aniya':
                        aniya_mother_house_index = i
                if grilled_house_index is None or aniya_mother_house_index is None:
                    continue
                if aniya_mother_house_index != grilled_house_index + 1:
                    continue
                
                # Constraint 4: Peter is The person whose mother's name is Holly.
                peter_house = None
                holly_mother_house = None
                for house in assignment:
                    if house['Name'] == 'Peter':
                        peter_house = house
                    if house['Mother'] == 'Holly':
                        holly_mother_house = house
                if peter_house is None or holly_mother_house is None:
                    continue
                if peter_house['Mother'] != 'Holly':
                    continue
                
                # Constraint 1: The person who loves the spaghetti eater and Peter are next to each other.
                spaghetti_eater_house = None
                peter_house_index = None
                for i in range(3):
                    if assignment[i]['Food'] == 'spaghetti':
                        spaghetti_eater_house = i
                    if assignment[i]['Name'] == 'Peter':
                        peter_house_index = i
                if spaghetti_eater_house is None or peter_house_index is None:
                    continue
                if abs(spaghetti_eater_house - peter_house_index) != 1:
                    continue
                
                # If all constraints are satisfied, prepare the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Food"],
                        "rows": []
                    }
                }
                for house in assignment:
                    solution["solution"]["rows"].append([
                        house['House'],
                        house['Name'],
                        house['Mother'],
                        house['Food']
                    ])
                return solution
    
    return {"solution": {"header": ["House", "Name", "Mother", "Food"], "rows": []}}

# Solve the puzzle and print the solution as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))