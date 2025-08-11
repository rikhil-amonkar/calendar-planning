import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    names = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high school']
    occupations = ['teacher', 'doctor', 'engineer']
    houses = ['1', '2', '3']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for edu_perm in permutations(educations):
            for occ_perm in permutations(occupations):
                # Assign attributes to houses
                solution = []
                for i in range(3):
                    house = {
                        'House': str(i+1),
                        'Name': name_perm[i],
                        'education': edu_perm[i],
                        'occupation': occ_perm[i]
                    }
                    solution.append(house)
                
                # Check all constraints
                valid = True
                
                # Constraint 1: The teacher is directly left of the associate's degree
                teacher_left_of_associate = False
                for i in range(2):
                    if solution[i]['occupation'] == 'teacher' and solution[i+1]['education'] == 'associate':
                        teacher_left_of_associate = True
                        break
                if not teacher_left_of_associate:
                    valid = False
                    continue
                
                # Constraint 2: The associate's degree and Eric are next to each other
                associate_and_eric_next = False
                for i in range(3):
                    if solution[i]['education'] == 'associate':
                        # Check left neighbor
                        if i > 0 and solution[i-1]['Name'] == 'Eric':
                            associate_and_eric_next = True
                            break
                        # Check right neighbor
                        if i < 2 and solution[i+1]['Name'] == 'Eric':
                            associate_and_eric_next = True
                            break
                if not associate_and_eric_next:
                    valid = False
                    continue
                
                # Constraint 3: Peter has a high school diploma
                peter_high_school = False
                for house in solution:
                    if house['Name'] == 'Peter' and house['education'] == 'high school':
                        peter_high_school = True
                        break
                if not peter_high_school:
                    valid = False
                    continue
                
                # Constraint 4: The doctor has a bachelor's degree
                doctor_bachelor = True
                for house in solution:
                    if house['occupation'] == 'doctor' and house['education'] != 'bachelor':
                        doctor_bachelor = False
                        break
                if not doctor_bachelor:
                    valid = False
                    continue
                
                if valid:
                    # Prepare the output
                    output = {
                        "solution": {
                            "header": ["House", "Name", "education", "occupation"],
                            "rows": []
                        }
                    }
                    for house in solution:
                        row = [
                            house['House'],
                            house['Name'],
                            house['education'],
                            house['occupation']
                        ]
                        output["solution"]["rows"].append(row)
                    return output
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result
solution = solve_puzzle()
print(json.dumps(solution, indent=2))