import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'Name': ['Eric', 'Peter', 'Arnold'],
        'Drink': ['milk', 'water', 'tea'],
        'Vacation': ['mountain', 'city', 'beach'],
        'HouseStyle': ['colonial', 'victorian', 'ranch'],
        'Animal': ['cat', 'bird', 'horse'],
        'Birthday': ['jan', 'sept', 'april']
    }
    
    # Generate all possible permutations for each category
    name_perms = permutations(categories['Name'])
    drink_perms = permutations(categories['Drink'])
    vacation_perms = permutations(categories['Vacation'])
    house_perms = permutations(categories['HouseStyle'])
    animal_perms = permutations(categories['Animal'])
    birthday_perms = permutations(categories['Birthday'])
    
    # Iterate through all possible combinations
    for names in name_perms:
        for drinks in drink_perms:
            for vacations in vacation_perms:
                for houses in house_perms:
                    for animals in animal_perms:
                        for birthdays in birthday_perms:
                            # Assign each attribute to houses 1, 2, 3
                            solution = {
                                1: {
                                    'Name': names[0],
                                    'Drink': drinks[0],
                                    'Vacation': vacations[0],
                                    'HouseStyle': houses[0],
                                    'Animal': animals[0],
                                    'Birthday': birthdays[0]
                                },
                                2: {
                                    'Name': names[1],
                                    'Drink': drinks[1],
                                    'Vacation': vacations[1],
                                    'HouseStyle': houses[1],
                                    'Animal': animals[1],
                                    'Birthday': birthdays[1]
                                },
                                3: {
                                    'Name': names[2],
                                    'Drink': drinks[2],
                                    'Vacation': vacations[2],
                                    'HouseStyle': houses[2],
                                    'Animal': animals[2],
                                    'Birthday': birthdays[2]
                                }
                            }
                            
                            # Check all constraints
                            # Constraint 1: colonial is left of milk
                            colonial_pos = None
                            milk_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['HouseStyle'] == 'colonial':
                                    colonial_pos = i
                                if solution[i]['Drink'] == 'milk':
                                    milk_pos = i
                            if colonial_pos is None or milk_pos is None or colonial_pos >= milk_pos:
                                continue
                            
                            # Constraint 2: city is directly left of victorian
                            city_pos = None
                            victorian_pos = None
                            for i in [1, 2]:
                                if solution[i]['Vacation'] == 'city':
                                    city_pos = i
                                    if solution[i+1]['HouseStyle'] == 'victorian':
                                        victorian_pos = i+1
                            if city_pos is None or victorian_pos is None or city_pos + 1 != victorian_pos:
                                continue
                            
                            # Constraint 3: jan is directly left of cat
                            jan_pos = None
                            cat_pos = None
                            for i in [1, 2]:
                                if solution[i]['Birthday'] == 'jan':
                                    jan_pos = i
                                    if solution[i+1]['Animal'] == 'cat':
                                        cat_pos = i+1
                            if jan_pos is None or cat_pos is None or jan_pos + 1 != cat_pos:
                                continue
                            
                            # Constraint 4: water drinker enjoys mountain
                            for i in [1, 2, 3]:
                                if solution[i]['Drink'] == 'water' and solution[i]['Vacation'] != 'mountain':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # Constraint 5: horse is Peter
                            for i in [1, 2, 3]:
                                if solution[i]['Animal'] == 'horse' and solution[i]['Name'] != 'Peter':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # Constraint 6: victorian is right of beach
                            beach_pos = None
                            victorian_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['Vacation'] == 'beach':
                                    beach_pos = i
                                if solution[i]['HouseStyle'] == 'victorian':
                                    victorian_pos = i
                            if beach_pos is None or victorian_pos is None or beach_pos >= victorian_pos:
                                continue
                            
                            # Constraint 7: Peter prefers city
                            peter_city = False
                            for i in [1, 2, 3]:
                                if solution[i]['Name'] == 'Peter' and solution[i]['Vacation'] == 'city':
                                    peter_city = True
                                    break
                            if not peter_city:
                                continue
                            
                            # Constraint 8: mountain vacation is april birthday
                            for i in [1, 2, 3]:
                                if solution[i]['Vacation'] == 'mountain' and solution[i]['Birthday'] != 'april':
                                    break
                            else:
                                pass
                            else:
                                continue
                            
                            # Constraint 9: Eric drinks water
                            eric_water = False
                            for i in [1, 2, 3]:
                                if solution[i]['Name'] == 'Eric' and solution[i]['Drink'] == 'water':
                                    eric_water = True
                                    break
                            if not eric_water:
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                                    "rows": [
                                        ["1", solution[1]['Name'], solution[1]['Drink'], solution[1]['Vacation'], solution[1]['HouseStyle'], solution[1]['Animal'], solution[1]['Birthday']],
                                        ["2", solution[2]['Name'], solution[2]['Drink'], solution[2]['Vacation'], solution[2]['HouseStyle'], solution[2]['Animal'], solution[2]['Birthday']],
                                        ["3", solution[3]['Name'], solution[3]['Drink'], solution[3]['Vacation'], solution[3]['HouseStyle'], solution[3]['Animal'], solution[3]['Birthday']]
                                    ]
                                }
                            }
                            return output
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))