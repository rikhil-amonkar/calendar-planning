import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high school']
    occupations = ['teacher', 'doctor', 'engineer']
    houses = ['1', '2', '3']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for edu_perm in permutations(educations):
            for occ_perm in permutations(occupations):
                # Create a list of houses with their attributes
                solution = [
                    {'House': '1', 'Name': name_perm[0], 'Education': edu_perm[0], 'Occupation': occ_perm[0]},
                    {'House': '2', 'Name': name_perm[1], 'Education': edu_perm[1], 'Occupation': occ_perm[1]},
                    {'House': '3', 'Name': name_perm[2], 'Education': edu_perm[2], 'Occupation': occ_perm[2]}
                ]
                
                # Check all constraints
                # Constraint 1: The teacher is directly left of the associate's degree
                teacher_left_associate = False
                for i in range(2):
                    if solution[i]['Occupation'] == 'teacher' and solution[i+1]['Education'] == 'associate':
                        teacher_left_associate = True
                        break
                if not teacher_left_associate:
                    continue
                
                # Constraint 2: The person with associate's degree and Eric are next to each other
                associate_house = None
                eric_house = None
                for house in solution:
                    if house['Education'] == 'associate':
                        associate_house = int(house['House'])
                    if house['Name'] == 'Eric':
                        eric_house = int(house['House'])
                if abs(associate_house - eric_house) != 1:
                    continue
                
                # Constraint 3: Peter has a high school diploma
                peter_high_school = False
                for house in solution:
                    if house['Name'] == 'Peter' and house['Education'] == 'high school':
                        peter_high_school = True
                        break
                if not peter_high_school:
                    continue
                
                # Constraint 4: The doctor has a bachelor's degree
                doctor_bachelor = True
                for house in solution:
                    if house['Occupation'] == 'doctor' and house['Education'] != 'bachelor':
                        doctor_bachelor = False
                        break
                if not doctor_bachelor:
                    continue
                
                # If all constraints are satisfied, format the solution
                rows = []
                for house in solution:
                    rows.append([
                        house['House'],
                        house['Name'],
                        house['Education'],
                        house['Occupation']
                    ])
                
                output = {
                    "solution": {
                        "header": ["House", "Name", "Education", "Occupation"],
                        "rows": rows
                    }
                }
                return json.dumps(output, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())