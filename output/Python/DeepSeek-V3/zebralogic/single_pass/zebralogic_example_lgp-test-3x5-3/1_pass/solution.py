import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'Name': ['Eric', 'Peter', 'Arnold'],
        'smoothie': ['cherry', 'watermelon', 'desert'],
        'flower': ['carnations', 'lilies', 'daffodils'],
        'animal': ['cat', 'horse', 'bird'],
        'hobby': ['photography', 'cooking', 'gardening']
    }
    
    # Generate all possible permutations for each category
    name_perms = permutations(categories['Name'])
    smoothie_perms = permutations(categories['smoothie'])
    flower_perms = permutations(categories['flower'])
    animal_perms = permutations(categories['animal'])
    hobby_perms = permutations(categories['hobby'])
    
    # Iterate through all possible combinations
    for names in name_perms:
        for smoothies in smoothie_perms:
            for flowers in flower_perms:
                for animals in animal_perms:
                    for hobbies in hobby_perms:
                        # Assign each permutation to houses 1-3
                        solution = []
                        for i in range(3):
                            house = {
                                'House': str(i+1),
                                'Name': names[i],
                                'smoothie': smoothies[i],
                                'flower': flowers[i],
                                'animal': animals[i],
                                'hobby': hobbies[i]
                            }
                            solution.append(house)
                        
                        # Check all clues
                        valid = True
                        
                        # Clue 8: The photography enthusiast is Eric.
                        for house in solution:
                            if house['Name'] == 'Eric' and house['hobby'] != 'photography':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 1: The person who keeps horses and the photography enthusiast are next to each other.
                        horse_houses = [h for h in solution if h['animal'] == 'horse']
                        photo_houses = [h for h in solution if h['hobby'] == 'photography']
                        if len(horse_houses) != 1 or len(photo_houses) != 1:
                            valid = False
                            continue
                        horse_house = horse_houses[0]
                        photo_house = photo_houses[0]
                        if abs(int(horse_house['House']) - int(photo_house['House'])) != 1:
                            valid = False
                            continue
                        
                        # Clue 2: The bird keeper is the person who likes Cherry smoothies.
                        for house in solution:
                            if house['animal'] == 'bird' and house['smoothie'] != 'cherry':
                                valid = False
                                break
                            if house['animal'] != 'bird' and house['smoothie'] == 'cherry':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 3: The person who loves cooking is the Desert smoothie lover.
                        for house in solution:
                            if house['hobby'] == 'cooking' and house['smoothie'] != 'desert':
                                valid = False
                                break
                            if house['hobby'] != 'cooking' and house['smoothie'] == 'desert':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
                        for house in solution:
                            if house['hobby'] == 'gardening' and house['flower'] != 'carnations':
                                valid = False
                                break
                            if house['hobby'] != 'gardening' and house['flower'] == 'carnations':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 5: The person who loves cooking is directly left of Peter.
                        cooking_house = None
                        peter_house = None
                        for house in solution:
                            if house['hobby'] == 'cooking':
                                cooking_house = house
                            if house['Name'] == 'Peter':
                                peter_house = house
                        if not cooking_house or not peter_house:
                            valid = False
                            continue
                        if int(cooking_house['House']) + 1 != int(peter_house['House']):
                            valid = False
                            continue
                        
                        # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
                        for house in solution:
                            if house['flower'] == 'daffodils' and house['smoothie'] != 'desert':
                                valid = False
                                break
                            if house['flower'] != 'daffodils' and house['smoothie'] == 'desert':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
                        for house in solution:
                            if house['smoothie'] == 'watermelon' and house['animal'] != 'horse':
                                valid = False
                                break
                            if house['smoothie'] != 'watermelon' and house['animal'] == 'horse':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # If all clues are satisfied, return the solution
                        if valid:
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "smoothie", "flower", "animal", "hobby"],
                                    "rows": []
                                }
                            }
                            for house in sorted(solution, key=lambda x: int(x['House'])):
                                output["solution"]["rows"].append([
                                    house['House'],
                                    house['Name'],
                                    house['smoothie'],
                                    house['flower'],
                                    house['animal'],
                                    house['hobby']
                                ])
                            return json.dumps(output, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())