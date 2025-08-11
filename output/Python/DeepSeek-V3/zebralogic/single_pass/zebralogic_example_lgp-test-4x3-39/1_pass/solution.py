import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    hair_colors = ['blonde', 'black', 'red', 'brown']
    sports = ['swimming', 'soccer', 'basketball', 'tennis']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for sport_perm in permutations(sports):
                # Assign each attribute to houses
                assignment = []
                for i in range(4):
                    assignment.append({
                        'House': houses[i],
                        'Name': name_perm[i],
                        'HairColor': hair_perm[i],
                        'Sport': sport_perm[i]
                    })
                
                # Check all constraints
                valid = True
                
                # Constraint 1: Soccer is not in house 2
                if assignment[1]['Sport'] == 'soccer':
                    valid = False
                
                # Constraint 2: Eric has blonde hair
                for house in assignment:
                    if house['Name'] == 'Eric' and house['HairColor'] != 'blonde':
                        valid = False
                
                # Constraint 3: Blonde is right of basketball
                basketball_houses = [h for h in assignment if h['Sport'] == 'basketball']
                blonde_houses = [h for h in assignment if h['HairColor'] == 'blonde']
                if basketball_houses and blonde_houses:
                    if int(basketball_houses[0]['House']) > int(blonde_houses[0]['House']):
                        valid = False
                else:
                    valid = False
                
                # Constraint 4: Black hair loves tennis
                for house in assignment:
                    if house['HairColor'] == 'black' and house['Sport'] != 'tennis':
                        valid = False
                
                # Constraint 5: Arnold is left of red hair
                arnold_house = next((h for h in assignment if h['Name'] == 'Arnold'), None)
                red_hair_house = next((h for h in assignment if h['HairColor'] == 'red'), None)
                if arnold_house and red_hair_house:
                    if int(arnold_house['House']) > int(red_hair_house['House']):
                        valid = False
                else:
                    valid = False
                
                # Constraint 6: Alice loves swimming
                for house in assignment:
                    if house['Name'] == 'Alice' and house['Sport'] != 'swimming':
                        valid = False
                
                # Constraint 7: Red is directly left of black
                for i in range(3):
                    if assignment[i]['HairColor'] == 'red' and assignment[i+1]['HairColor'] == 'black':
                        break
                else:
                    valid = False
                
                if valid:
                    # Prepare the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "Sport"],
                            "rows": []
                        }
                    }
                    for house in sorted(assignment, key=lambda x: int(x['House'])):
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['HairColor'],
                            house['Sport']
                        ])
                    return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the solution as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))