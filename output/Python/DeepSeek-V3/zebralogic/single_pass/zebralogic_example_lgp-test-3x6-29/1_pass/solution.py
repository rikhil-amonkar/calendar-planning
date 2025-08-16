import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'Name': ['Arnold', 'Peter', 'Eric'],
        'Animal': ['bird', 'horse', 'cat'],
        'Birthday': ['jan', 'sept', 'april'],
        'Hobby': ['photography', 'cooking', 'gardening'],
        'Drink': ['milk', 'water', 'tea'],
        'HairColor': ['black', 'brown', 'blonde']
    }
    
    # Generate all possible permutations for each house
    for name1, name2, name3 in permutations(categories['Name']):
        for animal1, animal2, animal3 in permutations(categories['Animal']):
            for bday1, bday2, bday3 in permutations(categories['Birthday']):
                for hobby1, hobby2, hobby3 in permutations(categories['Hobby']):
                    for drink1, drink2, drink3 in permutations(categories['Drink']):
                        for hair1, hair2, hair3 in permutations(categories['HairColor']):
                            # Create house assignments
                            houses = [
                                {
                                    'House': '1',
                                    'Name': name1,
                                    'Animal': animal1,
                                    'Birthday': bday1,
                                    'Hobby': hobby1,
                                    'Drink': drink1,
                                    'HairColor': hair1
                                },
                                {
                                    'House': '2',
                                    'Name': name2,
                                    'Animal': animal2,
                                    'Birthday': bday2,
                                    'Hobby': hobby2,
                                    'Drink': drink2,
                                    'HairColor': hair2
                                },
                                {
                                    'House': '3',
                                    'Name': name3,
                                    'Animal': animal3,
                                    'Birthday': bday3,
                                    'Hobby': hobby3,
                                    'Drink': drink3,
                                    'HairColor': hair3
                                }
                            ]
                            
                            # Check all constraints
                            # Constraint 2: April is in house 3
                            if houses[2]['Birthday'] != 'april':
                                continue
                            
                            # Constraint 3: Eric is not in house 1
                            if houses[0]['Name'] == 'Eric':
                                continue
                            
                            # Constraint 4: Cat is in house 2
                            if houses[1]['Animal'] != 'cat':
                                continue
                            
                            # Constraint 7: Cat lover has brown hair
                            if houses[1]['Animal'] == 'cat' and houses[1]['HairColor'] != 'brown':
                                continue
                            
                            # Constraint 1: Brown hair loves cooking
                            for house in houses:
                                if house['HairColor'] == 'brown' and house['Hobby'] != 'cooking':
                                    break
                            else:
                                # Constraint 5: Blonde is left of milk
                                blonde_pos = None
                                milk_pos = None
                                for i, house in enumerate(houses):
                                    if house['HairColor'] == 'blonde':
                                        blonde_pos = i
                                    if house['Drink'] == 'milk':
                                        milk_pos = i
                                if blonde_pos is not None and milk_pos is not None and blonde_pos >= milk_pos:
                                    continue
                                
                                # Constraint 6: Gardening loves milk
                                for house in houses:
                                    if house['Hobby'] == 'gardening' and house['Drink'] != 'milk':
                                        break
                                else:
                                    # Constraint 8: Arnold is bird keeper
                                    for house in houses:
                                        if house['Name'] == 'Arnold' and house['Animal'] != 'bird':
                                            break
                                    else:
                                        # Constraint 9: Water drinker is photography enthusiast
                                        for house in houses:
                                            if house['Drink'] == 'water' and house['Hobby'] != 'photography':
                                                break
                                        else:
                                            # Constraint 10: September is directly left of Arnold
                                            arnold_pos = None
                                            sept_pos = None
                                            for i, house in enumerate(houses):
                                                if house['Name'] == 'Arnold':
                                                    arnold_pos = i
                                                if house['Birthday'] == 'sept':
                                                    sept_pos = i
                                            if arnold_pos is not None and sept_pos is not None and sept_pos + 1 == arnold_pos:
                                                # All constraints satisfied
                                                solution = {
                                                    "solution": {
                                                        "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                                                        "rows": [
                                                            [house['House'], house['Name'], house['Animal'], house['Birthday'], house['Hobby'], house['Drink'], house['HairColor']]
                                                            for house in houses
                                                        ]
                                                    }
                                                }
                                                return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())