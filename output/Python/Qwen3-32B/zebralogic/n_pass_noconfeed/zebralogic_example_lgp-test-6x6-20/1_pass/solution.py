import itertools
import json

# Define all possible values for each attribute
names = ['Alice', 'Peter', 'Eric', 'Bob', 'Arnold', 'Carol']
cigars = ['pall mall', 'yellow monster', 'dunhill', 'blue master', 'prince', 'blends']
music = ['hip hop', 'jazz', 'country', 'pop', 'classical', 'rock']
drinks = ['water', 'milk', 'boba tea', 'tea', 'root beer', 'coffee']
mothers = ['Kailyn', 'Penny', 'Janelle', 'Holly', 'Sarah', 'Aniya']
food = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew', 'grilled cheese']

# Generate valid Name permutations
valid_names = []
for p in itertools.permutations(names):
    eric_pos = p.index('Eric')
    carol_pos = p.index('Carol')
    if carol_pos == eric_pos + 1 and p[1] != 'Eric':  # Eric not in house 2 (index 1)
        valid_names.append(p)

# Iterate through each valid Name permutation
for name in valid_names:
    eric_pos = name.index('Eric')
    carol_pos = name.index('Carol')
    grilled_cheese_pos = carol_pos + 1  # Carol is directly left of grilled cheese
    
    # Generate valid MusicGenre permutations for this Name
    valid_music = []
    for m in itertools.permutations(music):
        if m[5] != 'classical':  # Classical in house 6 (index 5)
            continue
        if m[eric_pos] != 'country':  # Eric's music is country
            continue
        if m[2] == 'pop':  # Pop not in house 3 (index 2)
            continue
        rock_pos = m.index('rock')
        if rock_pos >= grilled_cheese_pos:  # Rock must be left of grilled cheese
            continue
        valid_music.append(m)
    
    # Iterate through each valid MusicGenre permutation
    for music_perm in valid_music:
        bob_pos = name.index('Bob')
        eric_drink_pos = name.index('Eric')
        remaining_drinks = ['water', 'milk', 'boba tea', 'root beer']
        remaining_positions = [i for i in range(6) if i not in [bob_pos, eric_drink_pos]]
        
        # Generate valid Drink permutations
        valid_drinks = []
        for d_perm in itertools.permutations(remaining_drinks):
            drink = [''] * 6
            drink[bob_pos] = 'coffee'
            drink[eric_drink_pos] = 'tea'
            for i, pos in enumerate(remaining_positions):
                drink[pos] = d_perm[i]
            # Check root beer not in house 5 (index 4)
            if drink[4] == 'root beer':
                continue
            valid_drinks.append(drink)
        
        # Iterate through each valid Drink permutation
        for drink_perm in valid_drinks:
            # Generate valid Mother permutations
            valid_mothers = []
            for m_perm in itertools.permutations(mothers):
                # Check Janelle's drink is milk
                janelle_pos = -1
                valid_janelle = True
                for i in range(6):
                    if m_perm[i] == 'Janelle':
                        if drink_perm[i] != 'milk':
                            valid_janelle = False
                            break
                        janelle_pos = i
                if not valid_janelle:
                    continue
                
                # Check Holly's position is after Carol
                try:
                    holly_pos = m_perm.index('Holly')
                except ValueError:
                    continue
                if holly_pos <= carol_pos:
                    continue
                
                # Check Arnold is after Kailyn's mother
                try:
                    kailyn_pos = m_perm.index('Kailyn')
                except ValueError:
                    continue
                arnold_pos = name.index('Arnold')
                if arnold_pos <= kailyn_pos:
                    continue
                
                # Check root beer is directly left of Janelle
                root_beer_left_janelle = True
                for i in range(6):
                    if drink_perm[i] == 'root beer':
                        if i+1 >= 6 or m_perm[i+1] != 'Janelle':
                            root_beer_left_janelle = False
                            break
                if not root_beer_left_janelle:
                    continue
                
                # Check hip hop is directly left of Kailyn
                hip_hop_left_kailyn = True
                for i in range(6):
                    if music_perm[i] == 'hip hop':
                        if i+1 >= 6 or m_perm[i+1] != 'Kailyn':
                            hip_hop_left_kailyn = False
                            break
                if not hip_hop_left_kailyn:
                    continue
                
                # Check Sarah's mother is directly left of jazz
                sarah_left_jazz = True
                for i in range(6):
                    if m_perm[i] == 'Sarah':
                        if i+1 >= 6 or music_perm[i+1] != 'jazz':
                            sarah_left_jazz = False
                            break
                if not sarah_left_jazz:
                    continue
                
                valid_mothers.append(m_perm)
            
            # Iterate through each valid Mother permutation
            for mother_perm in valid_mothers:
                # Generate valid Cigar permutations
                peter_pos = name.index('Peter')
                valid_cigars = []
                for c_perm in itertools.permutations(cigars):
                    if c_perm[peter_pos] != 'blends':  # Peter smokes blends
                        continue
                    if c_perm[1] == 'dunhill':  # Dunhill not in house 2 (index 1)
                        continue
                    
                    # Check Blue Master is directly right of water
                    blue_master_right_water = True
                    for i in range(6):
                        if drink_perm[i] == 'water':
                            if i+1 >= 6 or c_perm[i+1] != 'blue master':
                                blue_master_right_water = False
                                break
                    if not blue_master_right_water:
                        continue
                    
                    # Check two houses between Sarah and Yellow Monster
                    try:
                        sarah_mother_pos = mother_perm.index('Sarah')
                    except ValueError:
                        continue
                    try:
                        yellow_monster_pos = c_perm.index('yellow monster')
                    except ValueError:
                        continue
                    if abs(sarah_mother_pos - yellow_monster_pos) != 3:
                        continue
                    
                    valid_cigars.append(c_perm)
                
                # Iterate through each valid Cigar permutation
                for cigar_perm in valid_cigars:
                    # Generate valid Food permutations
                    fixed_food_pos = grilled_cheese_pos  # Carol is directly left of grilled cheese
                    remaining_food_positions = [i for i in range(6) if i != fixed_food_pos]
                    remaining_foods = ['soup', 'pizza', 'spaghetti', 'stir fry', 'stew']
                    valid_foods = []
                    for f_perm in itertools.permutations(remaining_foods):
                        food_perm = [''] * 6
                        food_perm[fixed_food_pos] = 'grilled cheese'
                        for i, pos in enumerate(remaining_food_positions):
                            food_perm[pos] = f_perm[i]
                        
                        # Check water drinker has stew
                        water_stew = True
                        for i in range(6):
                            if drink_perm[i] == 'water' and food_perm[i] != 'stew':
                                water_stew = False
                                break
                        if not water_stew:
                            continue
                        
                        # Check spaghetti is left of Peter
                        peter_pos_food = name.index('Peter')
                        spaghetti_left_peter = True
                        for i in range(6):
                            if food_perm[i] == 'spaghetti' and i >= peter_pos_food:
                                spaghetti_left_peter = False
                                break
                        if not spaghetti_left_peter:
                            continue
                        
                        # Check stir fry has Pall Mall to the right
                        stir_fry_pall_mall = True
                        for i in range(6):
                            if food_perm[i] == 'stir fry':
                                found = False
                                for j in range(i+1, 6):
                                    if cigar_perm[j] == 'pall mall':
                                        found = True
                                        break
                                if not found:
                                    stir_fry_pall_mall = False
                                    break
                        if not stir_fry_pall_mall:
                            continue
                        
                        valid_foods.append(food_perm)
                    
                    # Iterate through each valid Food permutation
                    for food_perm in valid_foods:
                        # Final checks
                        # Check rock is left of grilled cheese
                        rock_pos = music_perm.index('rock')
                        if rock_pos >= fixed_food_pos:
                            continue
                        
                        # Check hip hop is left of root beer
                        hip_hop_left_root_beer = True
                        for i in range(6):
                            if music_perm[i] == 'hip hop':
                                if i+1 >= 6 or drink_perm[i+1] != 'root beer':
                                    hip_hop_left_root_beer = False
                                    break
                        if not hip_hop_left_root_beer:
                            continue
                        
                        # All constraints satisfied, output the solution
                        solution_rows = []
                        for i in range(6):
                            solution_rows.append([
                                str(i+1), name[i], cigar_perm[i], music_perm[i],
                                drink_perm[i], mother_perm[i], food_perm[i]
                            ])
                        print(json.dumps({
                            "solution": {
                                "header": ["House", "Name", "Cigar", "MusicGenre", "Drink", "Mother", "Food"],
                                "rows": solution_rows
                            }
                        }))
                        exit()