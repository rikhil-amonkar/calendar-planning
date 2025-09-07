import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']
    foods = ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']
    heights = ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']
    drinks = ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']
    pets = ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']
    phones = ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']

    # Precompute all possible permutations for each category
    all_perms = {
        'name': list(permutations(names)),
        'food': list(permutations(foods)),
        'height': list(permutations(heights)),
        'drink': list(permutations(drinks)),
        'pet': list(permutations(pets)),
        'phone': list(permutations(phones))
    }

    # Apply constraints that fix specific values to specific houses
    # Clue 1: iPhone 13 in house 3
    phone_constraints = [lambda p: p[2] == 'iphone 13']
    
    # Clue 3: Soup in house 2
    food_constraints = [lambda f: f[1] == 'soup']
    
    # Clue 9: OnePlus 9 is Arnold
    name_phone_constraints = []
    
    # Clue 15: Samsung Galaxy S21 is Carol
    name_phone_constraints = []
    
    # Clue 13: Fish is Alice
    name_pet_constraints = []
    
    # Generate all possible assignments that satisfy the constraints
    solutions = []
    
    for name_perm in all_perms['name']:
        # Clue 9: OnePlus 9 is Arnold
        if 'Arnold' not in name_perm:
            continue
        arnold_index = name_perm.index('Arnold')
        
        # Clue 15: Samsung Galaxy S21 is Carol
        if 'Carol' not in name_perm:
            continue
        carol_index = name_perm.index('Carol')
        
        # Clue 13: Fish is Alice
        if 'Alice' not in name_perm:
            continue
        alice_index = name_perm.index('Alice')
        
        for food_perm in all_perms['food']:
            # Clue 3: Soup in house 2
            if food_perm[1] != 'soup':
                continue
                
            # Clue 16: Pizza lover is short
            if 'pizza' not in food_perm:
                continue
            pizza_index = food_perm.index('pizza')
            
            # Clue 23: Very short loves spaghetti
            if 'spaghetti' not in food_perm:
                continue
            spaghetti_index = food_perm.index('spaghetti')
            
            for height_perm in all_perms['height']:
                # Clue 2: Bob is tall
                if 'Bob' not in name_perm:
                    continue
                bob_index = name_perm.index('Bob')
                if height_perm[bob_index] != 'tall':
                    continue
                
                # Clue 7: Grilled cheese lover is tall
                if 'grilled cheese' not in food_perm:
                    continue
                grilled_cheese_index = food_perm.index('grilled cheese')
                if height_perm[grilled_cheese_index] != 'tall':
                    continue
                
                # Clue 16: Pizza lover is short
                if height_perm[pizza_index] != 'short':
                    continue
                
                # Clue 17: Arnold is very tall
                if height_perm[arnold_index] != 'very tall':
                    continue
                
                # Clue 21: Very tall not in second house
                if height_perm[1] == 'very tall':
                    continue
                
                # Clue 23: Very short loves spaghetti
                if height_perm[spaghetti_index] != 'very short':
                    continue
                
                # Clue 12: Super tall has fish
                if 'super tall' not in height_perm:
                    continue
                super_tall_index = height_perm.index('super tall')
                
                for drink_perm in all_perms['drink']:
                    # Clue 4: Root beer left of Xiaomi Mi 11
                    # Clue 8: Xiaomi Mi 11 is coffee drinker
                    if 'root beer' not in drink_perm or 'coffee' not in drink_perm:
                        continue
                    root_beer_index = drink_perm.index('root beer')
                    coffee_index = drink_perm.index('coffee')
                    
                    # Clue 6: Stir fry lover likes milk
                    if 'stir fry' not in food_perm or 'milk' not in drink_perm:
                        continue
                    stir_fry_index = food_perm.index('stir fry')
                    milk_index = drink_perm.index('milk')
                    if stir_fry_index != milk_index:
                        continue
                    
                    # Clue 14: Tea left of pizza lover
                    if 'tea' not in drink_perm:
                        continue
                    tea_index = drink_perm.index('tea')
                    if tea_index + 1 != pizza_index:
                        continue
                    
                    # Clue 19: Boba tea right of soup lover (soup in house 2)
                    if 'boba tea' not in drink_perm:
                        continue
                    boba_tea_index = drink_perm.index('boba tea')
                    if boba_tea_index <= 1:  # soup is in house 2 (index 1)
                        continue
                    
                    for pet_perm in all_perms['pet']:
                        # Clue 10: Rabbit not in fifth house
                        if pet_perm[4] == 'rabbit':
                            continue
                        
                        # Clue 12: Super tall has fish
                        if pet_perm[super_tall_index] != 'fish':
                            continue
                        
                        # Clue 13: Fish is Alice
                        if pet_perm[alice_index] != 'fish':
                            continue
                        
                        # Clue 20: Hamster not in fifth house
                        if pet_perm[4] == 'hamster':
                            continue
                        
                        # Clue 24: Bird left of spaghetti lover
                        if 'bird' not in pet_perm:
                            continue
                        bird_index = pet_perm.index('bird')
                        if bird_index >= spaghetti_index:
                            continue
                        
                        # Clue 25: Fish left of Eric
                        if 'Eric' not in name_perm or 'fish' not in pet_perm:
                            continue
                        eric_index = name_perm.index('Eric')
                        fish_index = pet_perm.index('fish')
                        if fish_index + 1 != eric_index:
                            continue
                        
                        # Clue 26: Dog owner likes milk
                        if 'dog' not in pet_perm:
                            continue
                        dog_index = pet_perm.index('dog')
                        if dog_index != milk_index:
                            continue
                        
                        for phone_perm in all_perms['phone']:
                            # Clue 1: iPhone 13 in house 3
                            if phone_perm[2] != 'iphone 13':
                                continue
                            
                            # Clue 4: Root beer left of Xiaomi Mi 11
                            if 'xiaomi mi 11' not in phone_perm:
                                continue
                            xiaomi_index = phone_perm.index('xiaomi mi 11')
                            if root_beer_index + 1 != xiaomi_index:
                                continue
                            
                            # Clue 5: Huawei P50 left of grilled cheese lover
                            if 'huawei p50' not in phone_perm:
                                continue
                            huawei_index = phone_perm.index('huawei p50')
                            if huawei_index + 1 != grilled_cheese_index:
                                continue
                            
                            # Clue 8: Xiaomi Mi 11 is coffee drinker
                            if phone_perm[coffee_index] != 'xiaomi mi 11':
                                continue
                            
                            # Clue 9: OnePlus 9 is Arnold
                            if phone_perm[arnold_index] != 'oneplus 9':
                                continue
                            
                            # Clue 11: Hamster right of Google Pixel 6
                            if 'google pixel 6' not in phone_perm or 'hamster' not in pet_perm:
                                continue
                            pixel_index = phone_perm.index('google pixel 6')
                            hamster_index = pet_perm.index('hamster')
                            if hamster_index <= pixel_index:
                                continue
                            
                            # Clue 15: Samsung Galaxy S21 is Carol
                            if phone_perm[carol_index] != 'samsung galaxy s21':
                                continue
                            
                            # Clue 18: Spaghetti eater uses Google Pixel 6
                            if phone_perm[spaghetti_index] != 'google pixel 6':
                                continue
                            
                            # Clue 22: Super tall left of Peter
                            if 'Peter' not in name_perm:
                                continue
                            peter_index = name_perm.index('Peter')
                            if super_tall_index >= peter_index:
                                continue
                            
                            # All constraints satisfied, found a solution
                            solution = {
                                'name': name_perm,
                                'food': food_perm,
                                'height': height_perm,
                                'drink': drink_perm,
                                'pet': pet_perm,
                                'phone': phone_perm
                            }
                            solutions.append(solution)
    
    # Format the solution as JSON
    if solutions:
        solution = solutions[0]
        rows = []
        for i in range(6):
            row = [
                str(i + 1),
                solution['name'][i],
                solution['food'][i],
                solution['height'][i],
                solution['drink'][i],
                solution['pet'][i],
                solution['phone'][i]
            ]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": rows
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()