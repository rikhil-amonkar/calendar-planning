import json
from itertools import permutations

def solve_puzzle():
    # Define possible values for each attribute
    names = ['Arnold', 'Eric']
    hair_colors = ['black', 'brown']
    sports = ['basketball', 'soccer']
    smoothies = ['desert', 'cherry']
    
    # Generate all possible permutations for two houses
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for sport_perm in permutations(sports):
                for smoothie_perm in permutations(smoothies):
                    # Create a candidate solution
                    solution = {
                        '1': {
                            'Name': name_perm[0],
                            'HairColor': hair_perm[0],
                            'FavoriteSport': sport_perm[0],
                            'Smoothie': smoothie_perm[0]
                        },
                        '2': {
                            'Name': name_perm[1],
                            'HairColor': hair_perm[1],
                            'FavoriteSport': sport_perm[1],
                            'Smoothie': smoothie_perm[1]
                        }
                    }
                    
                    # Check constraints
                    # Constraint 1: Desert smoothie lover is Arnold
                    if not ((solution['1']['Smoothie'] == 'desert' and solution['1']['Name'] == 'Arnold') or 
                            (solution['2']['Smoothie'] == 'desert' and solution['2']['Name'] == 'Arnold')):
                        continue
                    
                    # Constraint 2: Brown hair person loves basketball
                    if not ((solution['1']['HairColor'] == 'brown' and solution['1']['FavoriteSport'] == 'basketball') or 
                            (solution['2']['HairColor'] == 'brown' and solution['2']['FavoriteSport'] == 'basketball')):
                        continue
                    
                    # Constraint 3: Arnold is left of black hair person
                    arnold_house = None
                    black_hair_house = None
                    for house in ['1', '2']:
                        if solution[house]['Name'] == 'Arnold':
                            arnold_house = house
                        if solution[house]['HairColor'] == 'black':
                            black_hair_house = house
                    if arnold_house is None or black_hair_house is None or int(arnold_house) >= int(black_hair_house):
                        continue
                    
                    # If all constraints are satisfied, return the solution
                    result = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                            "rows": [
                                ["1", solution['1']['Name'], solution['1']['HairColor'], solution['1']['FavoriteSport'], solution['1']['Smoothie']],
                                ["2", solution['2']['Name'], solution['2']['HairColor'], solution['2']['FavoriteSport'], solution['2']['Smoothie']]
                            ]
                        }
                    }
                    return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())