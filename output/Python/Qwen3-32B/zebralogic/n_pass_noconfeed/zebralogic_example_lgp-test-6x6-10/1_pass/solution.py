import itertools
import json

# Define all possible attributes
names_list = ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']
foods_list = ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']
heights_list = ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']
drinks_list = ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']
pets_list = ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']
phones_list = ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']

# Generate all valid phone permutations where house 3 (index 2) is 'iphone 13'
valid_phone_perms = []
for p in itertools.permutations(phones_list):
    if p[2] == 'iphone 13':
        valid_phone_perms.append(p)

# Iterate through each valid phone permutation
for phone_perm in valid_phone_perms:
    arnold_phone_pos = phone_perm.index('oneplus 9')
    carol_phone_pos = phone_perm.index('samsung galaxy s21')
    
    # Generate all possible name permutations with Arnold and Carol in their positions
    remaining_names = ['Bob', 'Peter', 'Alice', 'Eric']
    all_indices = set(range(6))
    fixed_indices = {arnold_phone_pos, carol_phone_pos}
    remaining_indices = list(all_indices - fixed_indices)
    
    for name_rest_perm in itertools.permutations(remaining_names):
        names = [''] * 6
        names[arnold_phone_pos] = 'Arnold'
        names[carol_phone_pos] = 'Carol'
        for i, idx in enumerate(remaining_indices):
            names[idx] = name_rest_perm[i]
        
        # Check if Alice is directly left of Eric (clue 25)
        alice_pos = names.index('Alice')
        eric_pos = names.index('Eric')
        if not (alice_pos + 1 == eric_pos):
            continue
        
        # Check if Alice is to the left of Peter (clue 22)
        peter_pos = names.index('Peter')
        if not (alice_pos < peter_pos):
            continue
        
        # Check if Bob's house has 'huawei p50' directly left (clue 5)
        bob_pos = names.index('Bob')
        if bob_pos == 0 or phone_perm[bob_pos - 1] != 'huawei p50':
            continue
        
        # Food constraints
        bob_food = 'grilled cheese'
        google_pixel_pos = phone_perm.index('google pixel 6')
        fixed_foods = {
            1: 'soup',  # clue 3
            bob_pos: bob_food,
            google_pixel_pos: 'spaghetti'  # clue 18
        }
        if len(set(fixed_foods.values())) != len(fixed_foods):
            continue
        
        remaining_foods = [f for f in foods_list if f not in fixed_foods.values()]
        remaining_food_indices = [i for i in range(6) if i not in fixed_foods.keys()]
        
        for food_rest_perm in itertools.permutations(remaining_foods):
            foods = [''] * 6
            for k, v in fixed_foods.items():
                foods[k] = v
            for i, idx in enumerate(remaining_food_indices):
                foods[idx] = food_rest_perm[i]
            
            # Height constraints
            fixed_heights = {
                bob_pos: 'tall',  # clue 2
                arnold_phone_pos: 'very tall',  # clue 17
                alice_pos: 'super tall',  # clue 12
                google_pixel_pos: 'very short',  # clue 23
            }
            pizza_pos = foods.index('pizza')
            fixed_heights[pizza_pos] = 'short'  # clue 16
            
            if len(set(fixed_heights.values())) != len(fixed_heights):
                continue
            
            remaining_height_indices = [i for i in range(6) if i not in fixed_heights.keys()]
            remaining_height = [h for h in heights_list if h not in fixed_heights.values()][0]
            heights = [''] * 6
            for k, v in fixed_heights.items():
                heights[k] = v
            for idx in remaining_height_indices:
                heights[idx] = remaining_height
            
            # Drink constraints
            xiaomi_pos = phone_perm.index('xiaomi mi 11')
            if xiaomi_pos == 0:
                continue
            stir_fry_pos = foods.index('stir fry')
            pizza_pos = foods.index('pizza')
            if pizza_pos == 0:
                continue
            
            fixed_drinks = {
                xiaomi_pos: 'coffee',  # clue 8
                xiaomi_pos - 1: 'root beer',  # clue 4
                stir_fry_pos: 'milk',  # clue 6
                pizza_pos - 1: 'tea'  # clue 14
            }
            if len(set(fixed_drinks.values())) != len(fixed_drinks):
                continue
            
            remaining_drinks = [d for d in drinks_list if d not in fixed_drinks.values()]
            remaining_drink_indices = [i for i in range(6) if i not in fixed_drinks.keys()]
            
            for drink_rest_perm in itertools.permutations(remaining_drinks):
                drinks = [''] * 6
                for k, v in fixed_drinks.items():
                    drinks[k] = v
                for i, idx in enumerate(remaining_drink_indices):
                    drinks[idx] = drink_rest_perm[i]
                
                # Check boba tea is to the right of soup (clue 19)
                boba_pos = drinks.index('boba tea')
                if boba_pos < 2:  # house 3 is index 2
                    continue
                
                # Pet constraints
                fixed_pets = {
                    alice_pos: 'fish',  # clue 13
                    stir_fry_pos: 'dog'  # clue 6 and 26
                }
                remaining_pets = [p for p in pets_list if p not in fixed_pets.values()]
                remaining_pet_indices = [i for i in range(6) if i not in fixed_pets.keys()]
                
                for pet_rest_perm in itertools.permutations(remaining_pets):
                    pets = [''] * 6
                    for k, v in fixed_pets.items():
                        pets[k] = v
                    for i, idx in enumerate(remaining_pet_indices):
                        pets[idx] = pet_rest_perm[i]
                    
                    # Check hamster is right of Google Pixel 6 (clue 11)
                    google_pixel_idx = phone_perm.index('google pixel 6')
                    hamster_pos = pets.index('hamster')
                    if hamster_pos <= google_pixel_idx:
                        continue
                    
                    # Check hamster not in house 5 (index 4)
                    if hamster_pos == 4:
                        continue
                    
                    # Check rabbit not in house 5 (index 4)
                    rabbit_pos = pets.index('rabbit')
                    if rabbit_pos == 4:
                        continue
                    
                    # Check bird is left of spaghetti (clue 24)
                    bird_pos = pets.index('bird')
                    if bird_pos >= google_pixel_idx:
                        continue
                    
                    # All constraints satisfied
                    solution_rows = []
                    for house_idx in range(6):
                        house_num = str(house_idx + 1)
                        solution_rows.append([
                            house_num,
                            names[house_idx],
                            foods[house_idx],
                            heights[house_idx],
                            drinks[house_idx],
                            pets[house_idx],
                            phone_perm[house_idx]
                        ])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                            "rows": solution_rows
                        }
                    }
                    
                    print(json.dumps(solution))
                    exit()