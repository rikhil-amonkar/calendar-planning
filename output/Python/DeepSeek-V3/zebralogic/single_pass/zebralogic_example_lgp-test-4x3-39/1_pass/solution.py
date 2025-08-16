import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    hair_colors = ['blonde', 'black', 'red', 'brown']
    sports = ['swimming', 'soccer', 'basketball', 'tennis']
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for sport_perm in permutations(sports):
                # Assign each permutation to houses
                assignment = []
                for i in range(4):
                    assignment.append({
                        'House': str(i + 1),
                        'Name': name_perm[i],
                        'HairColor': hair_perm[i],
                        'FavoriteSport': sport_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Constraint 1: Soccer not in house 2
                if assignment[1]['FavoriteSport'] == 'soccer':
                    valid = False
                
                # Constraint 2: Eric has blonde hair
                for house in assignment:
                    if house['Name'] == 'Eric' and house['HairColor'] != 'blonde':
                        valid = False
                
                # Constraint 3: Blonde is right of basketball
                basketball_house = None
                blonde_house = None
                for house in assignment:
                    if house['FavoriteSport'] == 'basketball':
                        basketball_house = int(house['House'])
                    if house['HairColor'] == 'blonde':
                        blonde_house = int(house['House'])
                if basketball_house is None or blonde_house is None or blonde_house <= basketball_house:
                    valid = False
                
                # Constraint 4: Black hair loves tennis
                for house in assignment:
                    if house['HairColor'] == 'black' and house['FavoriteSport'] != 'tennis':
                        valid = False
                
                # Constraint 5: Arnold is left of red hair
                arnold_house = None
                red_house = None
                for house in assignment:
                    if house['Name'] == 'Arnold':
                        arnold_house = int(house['House'])
                    if house['HairColor'] == 'red':
                        red_house = int(house['House'])
                if arnold_house is None or red_house is None or arnold_house >= red_house:
                    valid = False
                
                # Constraint 6: Alice loves swimming
                for house in assignment:
                    if house['Name'] == 'Alice' and house['FavoriteSport'] != 'swimming':
                        valid = False
                
                # Constraint 7: Red is directly left of black
                red_house = None
                black_house = None
                for house in assignment:
                    if house['HairColor'] == 'red':
                        red_house = int(house['House'])
                    if house['HairColor'] == 'black':
                        black_house = int(house['House'])
                if red_house is None or black_house is None or black_house != red_house + 1:
                    valid = False
                
                if valid:
                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "FavoriteSport"],
                            "rows": []
                        }
                    }
                    for house in assignment:
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['HairColor'],
                            house['FavoriteSport']
                        ])
                    return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())