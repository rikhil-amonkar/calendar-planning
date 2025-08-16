import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
    car_models = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
    phone_models = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
    occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
    drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']

    # Initialize solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": []
        }
    }

    # We'll represent each house as a dictionary in a list
    for house in houses:
        solution["solution"]["rows"].append([house, None, None, None, None, None, None])

    # Helper function to get index of house (0-based)
    def house_index(house_str):
        return int(house_str) - 1

    # Apply clues one by one
    # Clue 17: Eric is in the fourth house.
    solution["solution"]["rows"][house_index('4')][1] = 'Eric'

    # Clue 14: Alice is the person who is an artist.
    # Clue 3: Alice uses samsung galaxy s21
    # Clue 4: Alice loves stir fry
    # So Alice has: name=Alice, phone=samsung galaxy s21, food=stir fry, occupation=artist

    # Clue 15: There is one house between Alice and the person who owns a Ford F-150.
    # Possible positions:
    # Alice in 1, ford in 3
    # Alice in 2, ford in 4
    # Alice in 3, ford in 5

    # Try possible positions for Alice
    for alice_pos in ['1', '2', '3']:
        ford_pos = str(int(alice_pos) + 2)
        # Create a temporary solution to test
        temp_solution = [row.copy() for row in solution["solution"]["rows"]]
        
        # Set Alice's attributes
        temp_solution[house_index(alice_pos)][1] = 'Alice'
        temp_solution[house_index(alice_pos)][2] = 'stir fry'
        temp_solution[house_index(alice_pos)][4] = 'samsung galaxy s21'
        temp_solution[house_index(alice_pos)][5] = 'artist'
        
        # Set ford f150
        temp_solution[house_index(ford_pos)][3] = 'ford f150'
        
        # Clue 7: Arnold is the doctor
        # Clue 16: Arnold owns toyota camry
        # Clue 11: doctor is directly left of oneplus 9 user
        # So Arnold is in house X, X+1 has oneplus 9
        
        # Try possible positions for Arnold
        for arnold_pos in ['1', '2', '3', '4']:
            oneplus_pos = str(int(arnold_pos) + 1)
            if oneplus_pos > '5':
                continue
            if temp_solution[house_index(arnold_pos)][1] is not None:
                continue  # position already taken
            
            temp_solution2 = [row.copy() for row in temp_solution]
            temp_solution2[house_index(arnold_pos)][1] = 'Arnold'
            temp_solution2[house_index(arnold_pos)][5] = 'doctor'
            temp_solution2[house_index(arnold_pos)][3] = 'toyota camry'
            
            # Clue 18: oneplus 9 user is lawyer
            temp_solution2[house_index(oneplus_pos)][4] = 'oneplus 9'
            temp_solution2[house_index(oneplus_pos)][5] = 'lawyer'
            
            # Clue 9: engineer owns bmw 3 series
            # Clue 6: bmw is left of tea drinker
            # Clue 13: google pixel 6 is tea drinker
            # So bmw is left of google pixel 6 user
            
            # Find positions for bmw and google pixel 6
            for bmw_pos in ['1', '2', '3', '4']:
                for tea_pos in range(int(bmw_pos) + 1, 6):
                    tea_pos_str = str(tea_pos)
                    if temp_solution2[house_index(bmw_pos)][3] is not None and temp_solution2[house_index(bmw_pos)][3] != 'bmw 3 series':
                        continue
                    if temp_solution2[house_index(tea_pos_str)][4] is not None and temp_solution2[house_index(tea_pos_str)][4] != 'google pixel 6':
                        continue
                    
                    temp_solution3 = [row.copy() for row in temp_solution2]
                    temp_solution3[house_index(bmw_pos)][3] = 'bmw 3 series'
                    temp_solution3[house_index(bmw_pos)][5] = 'engineer'
                    temp_solution3[house_index(tea_pos_str)][4] = 'google pixel 6'
                    temp_solution3[house_index(tea_pos_str)][6] = 'tea'
                    
                    # Clue 5: tea drinker is not in fifth house
                    if tea_pos_str == '5':
                        continue
                    
                    # Clue 8: iphone 13 user is coffee drinker
                    # Clue 10: stew eater uses iphone 13
                    # So stew eater uses iphone 13 and drinks coffee
                    for iphone_pos in ['1', '2', '3', '4', '5']:
                        if temp_solution3[house_index(iphone_pos)][4] is not None:
                            continue
                        temp_solution4 = [row.copy() for row in temp_solution3]
                        temp_solution4[house_index(iphone_pos)][4] = 'iphone 13'
                        temp_solution4[house_index(iphone_pos)][6] = 'coffee'
                        temp_solution4[house_index(iphone_pos)][2] = 'stew'
                        
                        # Clue 1: root beer lover owns honda civic
                        # Clue 12: honda civic is directly left of spaghetti eater
                        # So honda civic in X, spaghetti in X+1
                        for honda_pos in ['1', '2', '3', '4']:
                            spaghetti_pos = str(int(honda_pos) + 1)
                            if spaghetti_pos > '5':
                                continue
                            if temp_solution4[house_index(honda_pos)][3] is not None and temp_solution4[house_index(honda_pos)][3] != 'honda civic':
                                continue
                            if temp_solution4[house_index(spaghetti_pos)][2] is not None and temp_solution4[house_index(spaghetti_pos)][2] != 'spaghetti':
                                continue
                            
                            temp_solution5 = [row.copy() for row in temp_solution4]
                            temp_solution5[house_index(honda_pos)][3] = 'honda civic'
                            temp_solution5[house_index(honda_pos)][6] = 'root beer'
                            temp_solution5[house_index(spaghetti_pos)][2] = 'spaghetti'
                            
                            # Clue 2: milk drinker is directly left of grilled cheese eater
                            # Clue 19: grilled cheese eater is Peter
                            for milk_pos in ['1', '2', '3', '4']:
                                grill_pos = str(int(milk_pos) + 1)
                                if grill_pos > '5':
                                    continue
                                if temp_solution5[house_index(grill_pos)][1] is not None and temp_solution5[house_index(grill_pos)][1] != 'Peter':
                                    continue
                                if temp_solution5[house_index(grill_pos)][2] is not None and temp_solution5[house_index(grill_pos)][2] != 'grilled cheese':
                                    continue
                                
                                temp_solution6 = [row.copy() for row in temp_solution5]
                                temp_solution6[house_index(milk_pos)][6] = 'milk'
                                temp_solution6[house_index(grill_pos)][1] = 'Peter'
                                temp_solution6[house_index(grill_pos)][2] = 'grilled cheese'
                                
                                # Now assign remaining names and attributes
                                # Collect assigned names
                                assigned_names = set()
                                for row in temp_solution6:
                                    if row[1] is not None:
                                        assigned_names.add(row[1])
                                remaining_names = [n for n in names if n not in assigned_names]
                                
                                # Assign remaining names to empty slots
                                empty_slots = []
                                for i in range(5):
                                    if temp_solution6[i][1] is None:
                                        empty_slots.append(i)
                                
                                if len(remaining_names) != len(empty_slots):
                                    continue
                                
                                # Try all permutations of remaining names
                                for name_perm in permutations(remaining_names):
                                    temp_solution7 = [row.copy() for row in temp_solution6]
                                    for i, slot in enumerate(empty_slots):
                                        temp_solution7[slot][1] = name_perm[i]
                                    
                                    # Check if all names are assigned
                                    names_assigned = True
                                    for row in temp_solution7:
                                        if row[1] is None:
                                            names_assigned = False
                                            break
                                    if not names_assigned:
                                        continue
                                    
                                    # Assign remaining attributes
                                    # Check if all constraints are satisfied
                                    valid = True
                                    for row in temp_solution7:
                                        house_num = row[0]
                                        name = row[1]
                                        food = row[2]
                                        car = row[3]
                                        phone = row[4]
                                        occupation = row[5]
                                        drink = row[6]
                                        
                                        # Check all clues are satisfied
                                        # Clue 1: root beer lover owns honda civic
                                        if drink == 'root beer' and car != 'honda civic':
                                            valid = False
                                        if car == 'honda civic' and drink != 'root beer':
                                            valid = False
                                        
                                        # Clue 2: milk is directly left of grilled cheese
                                        # Already enforced
                                        
                                        # Clue 3: Alice uses samsung galaxy s21
                                        if name == 'Alice' and phone != 'samsung galaxy s21':
                                            valid = False
                                        
                                        # Clue 4: Alice loves stir fry
                                        if name == 'Alice' and food != 'stir fry':
                                            valid = False
                                        
                                        # Clue 5: tea not in fifth house
                                        if drink == 'tea' and house_num == '5':
                                            valid = False
                                        
                                        # Clue 6: bmw left of tea
                                        # Already enforced
                                        
                                        # Clue 7: Arnold is doctor
                                        if name == 'Arnold' and occupation != 'doctor':
                                            valid = False
                                        
                                        # Clue 8: iphone 13 is coffee
                                        if phone == 'iphone 13' and drink != 'coffee':
                                            valid = False
                                        
                                        # Clue 9: engineer owns bmw
                                        if occupation == 'engineer' and car != 'bmw 3 series':
                                            valid = False
                                        if car == 'bmw 3 series' and occupation != 'engineer':
                                            valid = False
                                        
                                        # Clue 10: stew eater uses iphone 13
                                        if food == 'stew' and phone != 'iphone 13':
                                            valid = False
                                        if phone == 'iphone 13' and food != 'stew':
                                            valid = False
                                        
                                        # Clue 11: doctor is directly left of oneplus 9
                                        # Already enforced
                                        
                                        # Clue 12: honda civic directly left of spaghetti
                                        # Already enforced
                                        
                                        # Clue 13: google pixel 6 is tea
                                        if phone == 'google pixel 6' and drink != 'tea':
                                            valid = False
                                        if drink == 'tea' and phone != 'google pixel 6':
                                            valid = False
                                        
                                        # Clue 14: Alice is artist
                                        if name == 'Alice' and occupation != 'artist':
                                            valid = False
                                        
                                        # Clue 15: one house between Alice and ford f150
                                        # Already enforced
                                        
                                        # Clue 16: Arnold owns toyota camry
                                        if name == 'Arnold' and car != 'toyota camry':
                                            valid = False
                                        
                                        # Clue 18: oneplus 9 is lawyer
                                        if phone == 'oneplus 9' and occupation != 'lawyer':
                                            valid = False
                                        if occupation == 'lawyer' and phone != 'oneplus 9':
                                            valid = False
                                        
                                        # Clue 19: grilled cheese is Peter
                                        if food == 'grilled cheese' and name != 'Peter':
                                            valid = False
                                    
                                    if not valid:
                                        continue
                                    
                                    # Fill in remaining attributes
                                    # Collect all possible options for each category
                                    all_foods = set(foods)
                                    all_cars = set(car_models)
                                    all_phones = set(phone_models)
                                    all_occupations = set(occupations)
                                    all_drinks = set(drinks)
                                    
                                    # Remove assigned values
                                    for row in temp_solution7:
                                        if row[2] is not None:
                                            all_foods.discard(row[2])
                                        if row[3] is not None:
                                            all_cars.discard(row[3])
                                        if row[4] is not None:
                                            all_phones.discard(row[4])
                                        if row[5] is not None:
                                            all_occupations.discard(row[5])
                                        if row[6] is not None:
                                            all_drinks.discard(row[6])
                                    
                                    # Assign remaining values
                                    for row in temp_solution7:
                                        if row[2] is None:
                                            if len(all_foods) == 1:
                                                row[2] = all_foods.pop()
                                        if row[3] is None:
                                            if len(all_cars) == 1:
                                                row[3] = all_cars.pop()
                                        if row[4] is None:
                                            if len(all_phones) == 1:
                                                row[4] = all_phones.pop()
                                        if row[5] is None:
                                            if len(all_occupations) == 1:
                                                row[5] = all_occupations.pop()
                                        if row[6] is None:
                                            if len(all_drinks) == 1:
                                                row[6] = all_drinks.pop()
                                    
                                    # Check if all attributes are filled
                                    complete = True
                                    for row in temp_solution7:
                                        if None in row:
                                            complete = False
                                            break
                                    
                                    if complete and valid:
                                        solution["solution"]["rows"] = temp_solution7
                                        return json.dumps(solution, indent=2)
    
    return json.dumps(solution, indent=2)

print(solve_puzzle())