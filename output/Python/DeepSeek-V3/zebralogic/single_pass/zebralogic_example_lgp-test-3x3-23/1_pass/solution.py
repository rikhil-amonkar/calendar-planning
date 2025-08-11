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
                # Assign each permutation to houses
                assignment = []
                for i in range(3):
                    house = {
                        'House': str(i + 1),
                        'Name': name_perm[i],
                        'Occupation': occ_perm[i],
                        'Hobby': hobby_perm[i]
                    }
                    assignment.append(house)

                # Check all constraints
                valid = True

                # Constraint 1: The person who is a doctor and Eric are next to each other.
                doctor_houses = [h for h in assignment if h['Occupation'] == 'doctor']
                eric_houses = [h for h in assignment if h['Name'] == 'Eric']
                if len(doctor_houses) != 1 or len(eric_houses) != 1:
                    valid = False
                else:
                    doctor_house = int(doctor_houses[0]['House'])
                    eric_house = int(eric_houses[0]['House'])
                    if abs(doctor_house - eric_house) != 1:
                        valid = False

                if not valid:
                    continue

                # Constraint 2: The person who loves cooking is directly left of the person who is a teacher.
                cooking_house = None
                teacher_house = None
                for h in assignment:
                    if h['Hobby'] == 'cooking':
                        cooking_house = int(h['House'])
                    if h['Occupation'] == 'teacher':
                        teacher_house = int(h['House'])
                if cooking_house is None or teacher_house is None or cooking_house + 1 != teacher_house:
                    valid = False

                if not valid:
                    continue

                # Constraint 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
                gardening_house = None
                for h in assignment:
                    if h['Hobby'] == 'gardening':
                        gardening_house = int(h['House'])
                if gardening_house is None or int(doctor_houses[0]['House']) <= gardening_house:
                    valid = False

                if not valid:
                    continue

                # Constraint 4: The photography enthusiast is the person who is a teacher.
                for h in assignment:
                    if h['Hobby'] == 'photography' and h['Occupation'] != 'teacher':
                        valid = False
                    if h['Occupation'] == 'teacher' and h['Hobby'] != 'photography':
                        valid = False

                if not valid:
                    continue

                # Constraint 5: The person who is an engineer is Peter.
                for h in assignment:
                    if h['Occupation'] == 'engineer' and h['Name'] != 'Peter':
                        valid = False
                    if h['Name'] == 'Peter' and h['Occupation'] != 'engineer':
                        valid = False

                if not valid:
                    continue

                # If all constraints are satisfied, return the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Hobby"],
                        "rows": [
                            [h['House'], h['Name'], h['Occupation'], h['Hobby']] for h in assignment
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

    return json.dumps({"solution": {}})

print(solve_puzzle())