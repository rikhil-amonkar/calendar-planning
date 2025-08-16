import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Peter', 'Eric', 'Alice', 'Arnold']
    educations = ['bachelor', 'high school', 'associate', 'master']
    music_genres = ['jazz', 'rock', 'pop', 'classical']
    colors = ['green', 'red', 'yellow', 'white']
    flowers = ['lilies', 'carnations', 'daffodils', 'roses']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for edu_perm in permutations(educations):
            for music_perm in permutations(music_genres):
                for color_perm in permutations(colors):
                    for flower_perm in permutations(flowers):
                        # Create a dictionary to hold the current assignment
                        solution = {
                            1: {'Name': None, 'Education': None, 'MusicGenre': None, 'Color': None, 'Flower': None},
                            2: {'Name': None, 'Education': None, 'MusicGenre': None, 'Color': None, 'Flower': None},
                            3: {'Name': None, 'Education': None, 'MusicGenre': None, 'Color': None, 'Flower': None},
                            4: {'Name': None, 'Education': None, 'MusicGenre': None, 'Color': None, 'Flower': None}
                        }
                        
                        # Assign the current permutation to the houses
                        for i in range(4):
                            house = i + 1
                            solution[house]['Name'] = name_perm[i]
                            solution[house]['Education'] = edu_perm[i]
                            solution[house]['MusicGenre'] = music_perm[i]
                            solution[house]['Color'] = color_perm[i]
                            solution[house]['Flower'] = flower_perm[i]
                        
                        # Check all constraints
                        valid = True
                        
                        # Constraint 1: bachelor's degree loves daffodils
                        for house in solution:
                            if solution[house]['Education'] == 'bachelor':
                                if solution[house]['Flower'] != 'daffodils':
                                    valid = False
                                    break
                        if not valid:
                            continue
                        
                        # Constraint 2: carnations not in first house
                        if solution[1]['Flower'] == 'carnations':
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 3: master's degree is Alice
                        for house in solution:
                            if solution[house]['Education'] == 'master':
                                if solution[house]['Name'] != 'Alice':
                                    valid = False
                                    break
                        if not valid:
                            continue
                        
                        # Constraint 4: master's degree is directly left of classical music
                        master_house = None
                        classical_house = None
                        for house in solution:
                            if solution[house]['Education'] == 'master':
                                master_house = house
                            if solution[house]['MusicGenre'] == 'classical':
                                classical_house = house
                        if master_house is None or classical_house is None or classical_house != master_house + 1:
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 5: Eric is not in the second house
                        if solution[2]['Name'] == 'Eric':
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 6: Arnold is not in the third house
                        if solution[3]['Name'] == 'Arnold':
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 7: yellow is directly left of roses
                        yellow_house = None
                        roses_house = None
                        for house in solution:
                            if solution[house]['Color'] == 'yellow':
                                yellow_house = house
                            if solution[house]['Flower'] == 'roses':
                                roses_house = house
                        if yellow_house is None or roses_house is None or roses_house != yellow_house + 1:
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 8: pop music is in the second house
                        if solution[2]['MusicGenre'] != 'pop':
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 9: associate's degree is not in the fourth house
                        if solution[4]['Education'] == 'associate':
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 10: carnations not in the fourth house
                        if solution[4]['Flower'] == 'carnations':
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 11: red is directly left of white
                        red_house = None
                        white_house = None
                        for house in solution:
                            if solution[house]['Color'] == 'red':
                                red_house = house
                            if solution[house]['Color'] == 'white':
                                white_house = house
                        if red_house is None or white_house is None or white_house != red_house + 1:
                            valid = False
                        if not valid:
                            continue
                        
                        # Constraint 12: red color loves rock music
                        for house in solution:
                            if solution[house]['Color'] == 'red':
                                if solution[house]['MusicGenre'] != 'rock':
                                    valid = False
                                    break
                        if not valid:
                            continue
                        
                        # Constraint 13: Arnold loves yellow
                        for house in solution:
                            if solution[house]['Name'] == 'Arnold':
                                if solution[house]['Color'] != 'yellow':
                                    valid = False
                                    break
                        if not valid:
                            continue
                        
                        # Constraint 14: daffodils lover loves yellow
                        for house in solution:
                            if solution[house]['Flower'] == 'daffodils':
                                if solution[house]['Color'] != 'yellow':
                                    valid = False
                                    break
                        if not valid:
                            continue
                        
                        # If all constraints are satisfied, return the solution
                        if valid:
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                    "rows": []
                                }
                            }
                            for house in range(1, 5):
                                row = [
                                    str(house),
                                    solution[house]['Name'],
                                    solution[house]['Education'],
                                    solution[house]['MusicGenre'],
                                    solution[house]['Color'],
                                    solution[house]['Flower']
                                ]
                                result["solution"]["rows"].append(row)
                            return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())