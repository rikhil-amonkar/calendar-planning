import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    car_models = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']

    # Generate all possible permutations for names, occupations, and car models
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for car_perm in permutations(car_models):
                solution = {}
                valid = True

                # Assign initial values
                for i in range(6):
                    solution[i+1] = {
                        'Name': name_perm[i],
                        'Occupation': occ_perm[i],
                        'CarModel': car_perm[i]
                    }

                # Check constraints
                # Clue 1: Ford F-150 in house 5
                if solution[5]['CarModel'] != 'ford f150':
                    valid = False
                    continue

                # Clue 2: Chevrolet Silverado not in house 2
                if solution[2]['CarModel'] == 'chevrolet silverado':
                    valid = False
                    continue

                # Clue 3: Honda Civic and Peter next to each other
                peter_house = None
                honda_house = None
                for house in solution:
                    if solution[house]['Name'] == 'Peter':
                        peter_house = house
                    if solution[house]['CarModel'] == 'honda civic':
                        honda_house = house
                if peter_house is None or honda_house is None or abs(peter_house - honda_house) != 1:
                    valid = False
                    continue

                # Clue 4: Lawyer not in house 5
                if solution[5]['Occupation'] == 'lawyer':
                    valid = False
                    continue

                # Clue 5: Nurse directly left of artist
                nurse_house = None
                artist_house = None
                for house in solution:
                    if solution[house]['Occupation'] == 'nurse':
                        nurse_house = house
                    if solution[house]['Occupation'] == 'artist':
                        artist_house = house
                if nurse_house is None or artist_house is None or artist_house - nurse_house != 1:
                    valid = False
                    continue

                # Clue 6: Carol right of Eric
                eric_house = None
                carol_house = None
                for house in solution:
                    if solution[house]['Name'] == 'Eric':
                        eric_house = house
                    if solution[house]['Name'] == 'Carol':
                        carol_house = house
                if eric_house is None or carol_house is None or carol_house <= eric_house:
                    valid = False
                    continue

                # Clue 7: Doctor is Eric
                if solution[eric_house]['Occupation'] != 'doctor':
                    valid = False
                    continue

                # Clue 8: Teacher left of nurse
                teacher_house = None
                for house in solution:
                    if solution[house]['Occupation'] == 'teacher':
                        teacher_house = house
                if teacher_house is None or teacher_house >= nurse_house:
                    valid = False
                    continue

                # Clue 9: Carol not in house 6
                if solution[6]['Name'] == 'Carol':
                    valid = False
                    continue

                # Clue 10: Engineer is Bob
                bob_house = None
                for house in solution:
                    if solution[house]['Name'] == 'Bob':
                        bob_house = house
                if bob_house is None or solution[bob_house]['Occupation'] != 'engineer':
                    valid = False
                    continue

                # Clue 11: Toyota Camry is nurse
                if solution[nurse_house]['CarModel'] != 'toyota camry':
                    valid = False
                    continue

                # Clue 12: One house between Peter and lawyer
                lawyer_house = None
                for house in solution:
                    if solution[house]['Occupation'] == 'lawyer':
                        lawyer_house = house
                if lawyer_house is None or abs(peter_house - lawyer_house) != 2:
                    valid = False
                    continue

                # Clue 13: One house between Tesla Model 3 and Bob
                tesla_house = None
                for house in solution:
                    if solution[house]['CarModel'] == 'tesla model 3':
                        tesla_house = house
                if tesla_house is None or abs(tesla_house - bob_house) != 2:
                    valid = False
                    continue

                # Clue 14: Arnold is artist
                arnold_house = None
                for house in solution:
                    if solution[house]['Name'] == 'Arnold':
                        arnold_house = house
                if arnold_house is None or solution[arnold_house]['Occupation'] != 'artist':
                    valid = False
                    continue

                if valid:
                    # Prepare the output
                    output = {
                        "solution": {
                            "header": ["House", "Name", "Occupation", "CarModel"],
                            "rows": []
                        }
                    }
                    for house in sorted(solution.keys()):
                        row = [str(house)]
                        row.append(solution[house]['Name'])
                        row.append(solution[house]['Occupation'])
                        row.append(solution[house]['CarModel'])
                        output["solution"]["rows"].append(row)
                    return json.dumps(output, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())