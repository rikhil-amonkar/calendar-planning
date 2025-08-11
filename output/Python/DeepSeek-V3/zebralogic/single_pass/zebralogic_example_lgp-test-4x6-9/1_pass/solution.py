import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'House': ['1', '2', '3', '4'],
        'Name': ['Peter', 'Arnold', 'Eric', 'Alice'],
        'Flower': ['daffodils', 'carnations', 'roses', 'lilies'],
        'Height': ['very short', 'short', 'tall', 'average'],
        'Mother': ['Janelle', 'Kailyn', 'Holly', 'Aniya'],
        'Occupation': ['engineer', 'doctor', 'teacher', 'artist'],
        'Sport': ['swimming', 'basketball', 'tennis', 'soccer']
    }
    
    # Generate all possible permutations for each category
    for name_perm in permutations(categories['Name']):
        for flower_perm in permutations(categories['Flower']):
            for height_perm in permutations(categories['Height']):
                for mother_perm in permutations(categories['Mother']):
                    for occupation_perm in permutations(categories['Occupation']):
                        for sport_perm in permutations(categories['Sport']):
                            # Create a dictionary to hold the current assignment
                            solution = {
                                '1': {}, '2': {}, '3': {}, '4': {}
                            }
                            for i in range(4):
                                house = str(i+1)
                                solution[house]['Name'] = name_perm[i]
                                solution[house]['Flower'] = flower_perm[i]
                                solution[house]['Height'] = height_perm[i]
                                solution[house]['Mother'] = mother_perm[i]
                                solution[house]['Occupation'] = occupation_perm[i]
                                solution[house]['Sport'] = sport_perm[i]
                            
                            # Apply the constraints
                            valid = True
                            
                            # Clue 1: swimming -> roses
                            for house in solution:
                                if solution[house]['Sport'] == 'swimming':
                                    if solution[house]['Flower'] != 'roses':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 2: roses -> Eric
                            for house in solution:
                                if solution[house]['Flower'] == 'roses':
                                    if solution[house]['Name'] != 'Eric':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 3: Arnold is tall
                            for house in solution:
                                if solution[house]['Name'] == 'Arnold':
                                    if solution[house]['Height'] != 'tall':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 4: daffodils is right of engineer
                            engineer_house = None
                            daffodils_house = None
                            for house in solution:
                                if solution[house]['Occupation'] == 'engineer':
                                    engineer_house = int(house)
                                if solution[house]['Flower'] == 'daffodils':
                                    daffodils_house = int(house)
                            if engineer_house is not None and daffodils_house is not None:
                                if daffodils_house <= engineer_house:
                                    valid = False
                            if not valid:
                                continue
                            
                            # Clue 5: soccer -> short
                            for house in solution:
                                if solution[house]['Sport'] == 'soccer':
                                    if solution[house]['Height'] != 'short':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 6: teacher is in house 1
                            if solution['1']['Occupation'] != 'teacher':
                                valid = False
                            if not valid:
                                continue
                            
                            # Clue 7: Janelle -> carnations
                            for house in solution:
                                if solution[house]['Mother'] == 'Janelle':
                                    if solution[house]['Flower'] != 'carnations':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 8: basketball -> average height
                            for house in solution:
                                if solution[house]['Sport'] == 'basketball':
                                    if solution[house]['Height'] != 'average':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 9: Arnold not in house 3
                            if solution['3']['Name'] == 'Arnold':
                                valid = False
                            if not valid:
                                continue
                            
                            # Clue 10: Holly is right of average height
                            average_house = None
                            holly_house = None
                            for house in solution:
                                if solution[house]['Height'] == 'average':
                                    average_house = int(house)
                                if solution[house]['Mother'] == 'Holly':
                                    holly_house = int(house)
                            if average_house is not None and holly_house is not None:
                                if holly_house <= average_house:
                                    valid = False
                            if not valid:
                                continue
                            
                            # Clue 11: Peter is doctor
                            for house in solution:
                                if solution[house]['Name'] == 'Peter':
                                    if solution[house]['Occupation'] != 'doctor':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 12: Aniya is Alice
                            for house in solution:
                                if solution[house]['Mother'] == 'Aniya':
                                    if solution[house]['Name'] != 'Alice':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # Clue 13: Arnold loves lilies
                            for house in solution:
                                if solution[house]['Name'] == 'Arnold':
                                    if solution[house]['Flower'] != 'lilies':
                                        valid = False
                                        break
                            if not valid:
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            if valid:
                                # Prepare the output
                                output = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "Sport"],
                                        "rows": []
                                    }
                                }
                                for house in ['1', '2', '3', '4']:
                                    row = [house]
                                    for attr in output["solution"]["header"][1:]:
                                        row.append(solution[house][attr])
                                    output["solution"]["rows"].append(row)
                                return output
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result
solution = solve_puzzle()
print(json.dumps(solution, indent=2))