import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]
    names = ['Peter', 'Arnold', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    hobbies = ['cooking', 'photography', 'gardening']
    
    # Generate all possible permutations for each category
    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            for hobby_perm in itertools.permutations(hobbies):
                # Create a list of assignments for each house
                assignments = []
                for i in range(3):
                    assignments.append({
                        'House': str(i + 1),
                        'Name': name_perm[i],
                        'Occupation': occ_perm[i],
                        'Hobby': hobby_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Constraint 1: The doctor and Eric are next to each other
                doctor_houses = [a['House'] for a in assignments if a['Occupation'] == 'doctor']
                eric_houses = [a['House'] for a in assignments if a['Name'] == 'Eric']
                if len(doctor_houses) != 1 or len(eric_houses) != 1:
                    valid = False
                else:
                    doctor_house = int(doctor_houses[0])
                    eric_house = int(eric_houses[0])
                    if abs(doctor_house - eric_house) != 1:
                        valid = False
                
                # Constraint 2: cooking is directly left of teacher
                cooking_houses = [a['House'] for a in assignments if a['Hobby'] == 'cooking']
                teacher_houses = [a['House'] for a in assignments if a['Occupation'] == 'teacher']
                if len(cooking_houses) != 1 or len(teacher_houses) != 1:
                    valid = False
                else:
                    cooking_house = int(cooking_houses[0])
                    teacher_house = int(teacher_houses[0])
                    if cooking_house + 1 != teacher_house:
                        valid = False
                
                # Constraint 3: doctor is right of gardening
                gardening_houses = [a['House'] for a in assignments if a['Hobby'] == 'gardening']
                if len(gardening_houses) != 1:
                    valid = False
                else:
                    gardening_house = int(gardening_houses[0])
                    if gardening_house >= doctor_house:
                        valid = False
                
                # Constraint 4: photography enthusiast is the teacher
                for a in assignments:
                    if a['Occupation'] == 'teacher' and a['Hobby'] != 'photography':
                        valid = False
                    if a['Hobby'] == 'photography' and a['Occupation'] != 'teacher':
                        valid = False
                
                # Constraint 5: engineer is Peter
                for a in assignments:
                    if a['Occupation'] == 'engineer' and a['Name'] != 'Peter':
                        valid = False
                
                if valid:
                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Occupation", "Hobby"],
                            "rows": []
                        }
                    }
                    for a in assignments:
                        solution["solution"]["rows"].append([
                            a['House'],
                            a['Name'],
                            a['Occupation'],
                            a['Hobby']
                        ])
                    return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())