import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4']
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    flowers = ['daffodils', 'carnations', 'roses', 'lilies']
    heights = ['very short', 'short', 'tall', 'average']
    mothers = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
    occupations = ['engineer', 'doctor', 'teacher', 'artist']
    sports = ['swimming', 'basketball', 'tennis', 'soccer']

    # We'll represent each house as a dictionary with the categories as keys
    # We'll try all permutations until we find one that fits all constraints

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for flower_perm in permutations(flowers):
            for height_perm in permutations(heights):
                for mother_perm in permutations(mothers):
                    for occupation_perm in permutations(occupations):
                        for sport_perm in permutations(sports):
                            solution = []
                            for i in range(4):
                                house = {
                                    'House': str(i+1),
                                    'Name': name_perm[i],
                                    'Flower': flower_perm[i],
                                    'Height': height_perm[i],
                                    'Mother': mother_perm[i],
                                    'Occupation': occupation_perm[i],
                                    'FavoriteSport': sport_perm[i]
                                }
                                solution.append(house)
                            
                            # Check all constraints
                            valid = True
                            
                            # Constraint 2: The person who loves the rose bouquet is Eric.
                            rose_house = None
                            for house in solution:
                                if house['Flower'] == 'roses':
                                    rose_house = house
                                    break
                            if not rose_house or rose_house['Name'] != 'Eric':
                                valid = False
                                continue
                            
                            # Constraint 1: The person who loves swimming is the person who loves the rose bouquet.
                            if rose_house['FavoriteSport'] != 'swimming':
                                valid = False
                                continue
                            
                            # Constraint 3: Arnold is the person who is tall.
                            arnold_house = None
                            for house in solution:
                                if house['Name'] == 'Arnold':
                                    arnold_house = house
                                    break
                            if not arnold_house or arnold_house['Height'] != 'tall':
                                valid = False
                                continue
                            
                            # Constraint 13: Arnold loves lilies
                            if arnold_house['Flower'] != 'lilies':
                                valid = False
                                continue
                            
                            # Constraint 9: Arnold is not in the third house.
                            if arnold_house['House'] == '3':
                                valid = False
                                continue
                            
                            # Constraint 4: The person who loves daffodils is to the right of the engineer.
                            engineer_house = None
                            daffodil_house = None
                            for house in solution:
                                if house['Occupation'] == 'engineer':
                                    engineer_house = house
                                if house['Flower'] == 'daffodils':
                                    daffodil_house = house
                            if not engineer_house or not daffodil_house or int(daffodil_house['House']) <= int(engineer_house['House']):
                                valid = False
                                continue
                            
                            # Constraint 5: The person who loves soccer is the person who is short.
                            soccer_house = None
                            for house in solution:
                                if house['FavoriteSport'] == 'soccer':
                                    soccer_house = house
                                    break
                            if not soccer_house or soccer_house['Height'] != 'short':
                                valid = False
                                continue
                            
                            # Constraint 6: The person who is a teacher is in the first house.
                            if solution[0]['Occupation'] != 'teacher':
                                valid = False
                                continue
                            
                            # Constraint 7: The person whose mother is Janelle loves carnations.
                            janelle_house = None
                            for house in solution:
                                if house['Mother'] == 'Janelle':
                                    janelle_house = house
                                    break
                            if not janelle_house or janelle_house['Flower'] != 'carnations':
                                valid = False
                                continue
                            
                            # Constraint 8: The person who loves basketball has average height.
                            basketball_house = None
                            for house in solution:
                                if house['FavoriteSport'] == 'basketball':
                                    basketball_house = house
                                    break
                            if not basketball_house or basketball_house['Height'] != 'average':
                                valid = False
                                continue
                            
                            # Constraint 10: The person whose mother is Holly is to the right of the person with average height.
                            average_house = None
                            holly_house = None
                            for house in solution:
                                if house['Height'] == 'average':
                                    average_house = house
                                if house['Mother'] == 'Holly':
                                    holly_house = house
                            if not average_house or not holly_house or int(holly_house['House']) <= int(average_house['House']):
                                valid = False
                                continue
                            
                            # Constraint 11: Peter is the doctor.
                            peter_house = None
                            for house in solution:
                                if house['Name'] == 'Peter':
                                    peter_house = house
                                    break
                            if not peter_house or peter_house['Occupation'] != 'doctor':
                                valid = False
                                continue
                            
                            # Constraint 12: The person whose mother is Aniya is Alice.
                            aniya_house = None
                            for house in solution:
                                if house['Mother'] == 'Aniya':
                                    aniya_house = house
                                    break
                            if not aniya_house or aniya_house['Name'] != 'Alice':
                                valid = False
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            if valid:
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                        "rows": []
                                    }
                                }
                                for house in sorted(solution, key=lambda x: int(x['House'])):
                                    row = [
                                        house['House'],
                                        house['Name'],
                                        house['Flower'],
                                        house['Height'],
                                        house['Mother'],
                                        house['Occupation'],
                                        house['FavoriteSport']
                                    ]
                                    result["solution"]["rows"].append(row)
                                return result
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))