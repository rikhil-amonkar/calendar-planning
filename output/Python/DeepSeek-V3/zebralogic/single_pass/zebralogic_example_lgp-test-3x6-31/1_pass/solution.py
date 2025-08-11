import itertools
import json

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['milk', 'water', 'tea']
    vacations = ['mountain', 'city', 'beach']
    house_styles = ['colonial', 'victorian', 'ranch']
    animals = ['cat', 'bird', 'horse']
    months = ['jan', 'sept', 'april']
    
    # Generate all possible permutations for each attribute
    for name_perm in itertools.permutations(names):
        for drink_perm in itertools.permutations(drinks):
            for vacation_perm in itertools.permutations(vacations):
                for house_perm in itertools.permutations(house_styles):
                    for animal_perm in itertools.permutations(animals):
                        for month_perm in itertools.permutations(months):
                            # Assign each permutation to houses 1, 2, 3
                            solution = {
                                1: {
                                    'Name': name_perm[0],
                                    'favorite drink': drink_perm[0],
                                    'vacation': vacation_perm[0],
                                    'house style': house_perm[0],
                                    'animal': animal_perm[0],
                                    'birthday month': month_perm[0]
                                },
                                2: {
                                    'Name': name_perm[1],
                                    'favorite drink': drink_perm[1],
                                    'vacation': vacation_perm[1],
                                    'house style': house_perm[1],
                                    'animal': animal_perm[1],
                                    'birthday month': month_perm[1]
                                },
                                3: {
                                    'Name': name_perm[2],
                                    'favorite drink': drink_perm[2],
                                    'vacation': vacation_perm[2],
                                    'house style': house_perm[2],
                                    'animal': animal_perm[2],
                                    'birthday month': month_perm[2]
                                }
                            }
                            
                            # Check all constraints
                            # Constraint 1: colonial is left of milk
                            colonial_pos = None
                            milk_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['house style'] == 'colonial':
                                    colonial_pos = i
                                if solution[i]['favorite drink'] == 'milk':
                                    milk_pos = i
                            if colonial_pos is not None and milk_pos is not None:
                                if colonial_pos >= milk_pos:
                                    continue
                            
                            # Constraint 2: city is directly left of victorian
                            valid = False
                            for i in [1, 2]:
                                if solution[i]['vacation'] == 'city' and solution[i+1]['house style'] == 'victorian':
                                    valid = True
                                    break
                            if not valid:
                                continue
                            
                            # Constraint 3: jan is directly left of cat
                            valid = False
                            for i in [1, 2]:
                                if solution[i]['birthday month'] == 'jan' and solution[i+1]['animal'] == 'cat':
                                    valid = True
                                    break
                            if not valid:
                                continue
                            
                            # Constraint 4: water drinker enjoys mountain
                            for i in [1, 2, 3]:
                                if solution[i]['favorite drink'] == 'water' and solution[i]['vacation'] != 'mountain':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # Constraint 5: horse keeper is Peter
                            for i in [1, 2, 3]:
                                if solution[i]['animal'] == 'horse' and solution[i]['Name'] != 'Peter':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # Constraint 6: victorian is right of beach
                            beach_pos = None
                            victorian_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['vacation'] == 'beach':
                                    beach_pos = i
                                if solution[i]['house style'] == 'victorian':
                                    victorian_pos = i
                            if beach_pos is not None and victorian_pos is not None:
                                if beach_pos >= victorian_pos:
                                    continue
                            
                            # Constraint 7: Peter prefers city
                            for i in [1, 2, 3]:
                                if solution[i]['Name'] == 'Peter' and solution[i]['vacation'] != 'city':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # Constraint 8: mountain vacation's birthday is april
                            for i in [1, 2, 3]:
                                if solution[i]['vacation'] == 'mountain' and solution[i]['birthday month'] != 'april':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # Constraint 9: Eric drinks water
                            for i in [1, 2, 3]:
                                if solution[i]['Name'] == 'Eric' and solution[i]['favorite drink'] != 'water':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # If all constraints passed, return the solution
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "favorite drink", "vacation", "house style", "animal", "birthday month"],
                                    "rows": [
                                        ["1", solution[1]['Name'], solution[1]['favorite drink'], solution[1]['vacation'], solution[1]['house style'], solution[1]['animal'], solution[1]['birthday month']],
                                        ["2", solution[2]['Name'], solution[2]['favorite drink'], solution[2]['vacation'], solution[2]['house style'], solution[2]['animal'], solution[2]['birthday month']],
                                        ["3", solution[3]['Name'], solution[3]['favorite drink'], solution[3]['vacation'], solution[3]['house style'], solution[3]['animal'], solution[3]['birthday month']]
                                    ]
                                }
                            }
                            return json.dumps(output, indent=2)
    
    return json.dumps({"solution": {}})

print(solve_puzzle())