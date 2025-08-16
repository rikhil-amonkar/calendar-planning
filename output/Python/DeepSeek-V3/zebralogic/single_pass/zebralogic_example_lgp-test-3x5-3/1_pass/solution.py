import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3']
    names = ['Eric', 'Peter', 'Arnold']
    smoothies = ['cherry', 'watermelon', 'desert']
    flowers = ['carnations', 'lilies', 'daffodils']
    animals = ['cat', 'horse', 'bird']
    hobbies = ['photography', 'cooking', 'gardening']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for flower_perm in permutations(flowers):
                for animal_perm in permutations(animals):
                    for hobby_perm in permutations(hobbies):
                        # Assign each permutation to houses 1, 2, 3
                        assignment = {
                            '1': {
                                'Name': name_perm[0],
                                'Smoothie': smoothie_perm[0],
                                'Flower': flower_perm[0],
                                'Animal': animal_perm[0],
                                'Hobby': hobby_perm[0]
                            },
                            '2': {
                                'Name': name_perm[1],
                                'Smoothie': smoothie_perm[1],
                                'Flower': flower_perm[1],
                                'Animal': animal_perm[1],
                                'Hobby': hobby_perm[1]
                            },
                            '3': {
                                'Name': name_perm[2],
                                'Smoothie': smoothie_perm[2],
                                'Flower': flower_perm[2],
                                'Animal': animal_perm[2],
                                'Hobby': hobby_perm[2]
                            }
                        }
                        
                        # Check all constraints
                        # Constraint 8: The photography enthusiast is Eric.
                        eric_hobby = None
                        for house in houses:
                            if assignment[house]['Name'] == 'Eric':
                                eric_hobby = assignment[house]['Hobby']
                        if eric_hobby != 'photography':
                            continue
                        
                        # Constraint 1: The person who keeps horses and the photography enthusiast are next to each other.
                        horse_house = None
                        photo_house = None
                        for house in houses:
                            if assignment[house]['Animal'] == 'horse':
                                horse_house = int(house)
                            if assignment[house]['Hobby'] == 'photography':
                                photo_house = int(house)
                        if horse_house is None or photo_house is None or abs(horse_house - photo_house) != 1:
                            continue
                        
                        # Constraint 2: The bird keeper is the person who likes Cherry smoothies.
                        for house in houses:
                            if assignment[house]['Animal'] == 'bird' and assignment[house]['Smoothie'] != 'cherry':
                                break
                        else:
                            # Check that all bird keepers like cherry (and no non-bird keepers like cherry unless they have bird)
                            cherry_lovers = [h for h in houses if assignment[h]['Smoothie'] == 'cherry']
                            bird_keepers = [h for h in houses if assignment[h]['Animal'] == 'bird']
                            if set(cherry_lovers) != set(bird_keepers):
                                continue
                        # Constraint 3: The person who loves cooking is the Desert smoothie lover.
                        cooking_house = None
                        for house in houses:
                            if assignment[house]['Hobby'] == 'cooking':
                                cooking_house = house
                        if cooking_house is None or assignment[cooking_house]['Smoothie'] != 'desert':
                            continue
                        
                        # Constraint 4: The person who enjoys gardening is the person who loves a carnations arrangement.
                        for house in houses:
                            if assignment[house]['Hobby'] == 'gardening' and assignment[house]['Flower'] != 'carnations':
                                break
                        else:
                            # Check that all gardening hobbies have carnations and vice versa
                            gardening_houses = [h for h in houses if assignment[h]['Hobby'] == 'gardening']
                            carnation_houses = [h for h in houses if assignment[h]['Flower'] == 'carnations']
                            if set(gardening_houses) != set(carnation_houses):
                                continue
                        
                        # Constraint 5: The person who loves cooking is directly left of Peter.
                        cooking_house_idx = None
                        peter_house_idx = None
                        for house in houses:
                            if assignment[house]['Hobby'] == 'cooking':
                                cooking_house_idx = int(house)
                            if assignment[house]['Name'] == 'Peter':
                                peter_house_idx = int(house)
                        if cooking_house_idx is None or peter_house_idx is None or peter_house_idx - cooking_house_idx != 1:
                            continue
                        
                        # Constraint 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
                        for house in houses:
                            if assignment[house]['Flower'] == 'daffodils' and assignment[house]['Smoothie'] != 'desert':
                                break
                        else:
                            # Check that all daffodil lovers have desert smoothie and vice versa
                            daffodil_houses = [h for h in houses if assignment[h]['Flower'] == 'daffodils']
                            desert_houses = [h for h in houses if assignment[h]['Smoothie'] == 'desert']
                            if set(daffodil_houses) != set(desert_houses):
                                continue
                        
                        # Constraint 7: The Watermelon smoothie lover is the person who keeps horses.
                        for house in houses:
                            if assignment[house]['Smoothie'] == 'watermelon' and assignment[house]['Animal'] != 'horse':
                                break
                        else:
                            # Check that all watermelon lovers have horse and vice versa
                            watermelon_houses = [h for h in houses if assignment[h]['Smoothie'] == 'watermelon']
                            horse_houses = [h for h in houses if assignment[h]['Animal'] == 'horse']
                            if set(watermelon_houses) != set(horse_houses):
                                continue
                        
                        # If all constraints are satisfied, return the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                "rows": [
                                    ["1", assignment['1']['Name'], assignment['1']['Smoothie'], assignment['1']['Flower'], assignment['1']['Animal'], assignment['1']['Hobby']],
                                    ["2", assignment['2']['Name'], assignment['2']['Smoothie'], assignment['2']['Flower'], assignment['2']['Animal'], assignment['2']['Hobby']],
                                    ["3", assignment['3']['Name'], assignment['3']['Smoothie'], assignment['3']['Flower'], assignment['3']['Animal'], assignment['3']['Hobby']]
                                ]
                            }
                        }
                        return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())