import json

def solve_puzzle():
    # Categories
    names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    housestyles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    foods = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

    def check_all_constraints(houses):
        # Clue 1: Alice is in fifth house (index 4)
        if houses[4]['Name'] != 'Alice':
            return False
        # Clue 2: stir fry → colonial
        for i in range(6):
            if houses[i]['Food'] == 'stir fry' and houses[i]['HouseStyle'] != 'colonial':
                return False
        # Clue 3: Alice → spaghetti (already handled)
        if houses[4]['Food'] != 'spaghetti':
            return False
        # Clue 4: Arnold → stew
        for i in range(6):
            if houses[i]['Name'] == 'Arnold' and houses[i]['Food'] != 'stew':
                return False
        # Clue 5: one house between average height and Peter
        avg_height_house = None
        peter_house = None
        for i in range(6):
            if houses[i]['Height'] == 'average':
                avg_height_house = i
            if houses[i]['Name'] == 'Peter':
                peter_house = i
        if avg_height_house is None or peter_house is None or abs(avg_height_house - peter_house) != 2:
            return False
        # Clue 6: craftsman not in third house (index 2)
        if houses[2]['HouseStyle'] == 'craftsman':
            return False
        # Clue 7: average height → stir fry
        for i in range(6):
            if houses[i]['Height'] == 'average' and houses[i]['Food'] != 'stir fry':
                return False
        # Clue 8: beach → ranch
        for i in range(6):
            if houses[i]['Vacation'] == 'beach' and houses[i]['HouseStyle'] != 'ranch':
                return False
        # Clue 9: Eric in fourth house (index 3)
        if houses[3]['Name'] != 'Eric':
            return False
        # Clue 10: one house between colonial and camping
        colonial_house = None
        camping_house = None
        for i in range(6):
            if houses[i]['HouseStyle'] == 'colonial':
                colonial_house = i
            if houses[i]['Vacation'] == 'camping':
                camping_house = i
        if colonial_house is None or camping_house is None or abs(colonial_house - camping_house) != 2:
            return False
        # Clue 11: mountain → yellow monster
        for i in range(6):
            if houses[i]['Vacation'] == 'mountain' and houses[i]['Cigar'] != 'yellow monster':
                return False
        # Clue 12: mountain → very tall
        for i in range(6):
            if houses[i]['Vacation'] == 'mountain' and houses[i]['Height'] != 'very tall':
                return False
        # Clue 13: mountain and dunhill are next to each other
        for i in range(6):
            if houses[i]['Vacation'] == 'mountain':
                if (i > 0 and houses[i-1]['Cigar'] == 'dunhill') or (i < 5 and houses[i+1]['Cigar'] == 'dunhill'):
                    continue
                return False
        # Clue 14: spaghetti → Victorian (already handled)
        if houses[4]['HouseStyle'] != 'Victorian':
            return False
        # Clue 15: tall → beach
        for i in range(6):
            if houses[i]['Height'] == 'tall' and houses[i]['Vacation'] != 'beach':
                return False
        # Clue 16: tall is left of Victorian (house 5, index 4)
        for i in range(6):
            if houses[i]['Height'] == 'tall' and i >= 4:
                return False
        # Clue 17: stir fry is directly left of Bob
        stir_fry_house = None
        bob_house = None
        for i in range(6):
            if houses[i]['Food'] == 'stir fry':
                stir_fry_house = i
            if houses[i]['Name'] == 'Bob':
                bob_house = i
        if stir_fry_house is None or bob_house is None or bob_house != stir_fry_house + 1:
            return False
        # Clue 18: modern is left of Alice (house 5, index 4)
        for i in range(6):
            if houses[i]['HouseStyle'] == 'modern' and i >= 4:
                return False
        # Clue 19: craftsman is left of short
        craftsman_house = None
        short_house = None
        for i in range(6):
            if houses[i]['HouseStyle'] == 'craftsman':
                craftsman_house = i
            if houses[i]['Height'] == 'short':
                short_house = i
        if craftsman_house is None or short_house is None or craftsman_house >= short_house:
            return False
        # Clue 20: stir fry is left of Prince smoker
        stir_fry_house = None
        prince_house = None
        for i in range(6):
            if houses[i]['Food'] == 'stir fry':
                stir_fry_house = i
            if houses[i]['Cigar'] == 'prince':
                prince_house = i
        if stir_fry_house is None or prince_house is None or stir_fry_house >= prince_house:
            return False
        # Clue 21: grilled cheese and super tall have two houses between
        grilled_cheese_house = None
        super_tall_house = None
        for i in range(6):
            if houses[i]['Food'] == 'grilled cheese':
                grilled_cheese_house = i
            if houses[i]['Height'] == 'super tall':
                super_tall_house = i
        if grilled_cheese_house is None or super_tall_house is None or abs(grilled_cheese_house - super_tall_house) != 3:
            return False
        # Clue 22: ranch → blue master
        for i in range(6):
            if houses[i]['HouseStyle'] == 'ranch' and houses[i]['Cigar'] != 'blue master':
                return False
        # Clue 23: blends is directly left of blue master
        for i in range(6):
            if i < 5 and houses[i]['Cigar'] == 'blends' and houses[i+1]['Cigar'] != 'blue master':
                return False
            if i > 0 and houses[i]['Cigar'] == 'blue master' and houses[i-1]['Cigar'] != 'blends':
                return False
        # Clue 24: cultural → pizza
        for i in range(6):
            if houses[i]['Vacation'] == 'cultural' and houses[i]['Food'] != 'pizza':
                return False
        # Clue 25: pizza is left of cruise
        pizza_house = None
        cruise_house = None
        for i in range(6):
            if houses[i]['Food'] == 'pizza':
                pizza_house = i
            if houses[i]['Vacation'] == 'cruise':
                cruise_house = i
        if pizza_house is None or cruise_house is None or pizza_house >= cruise_house:
            return False
        return True

    def backtrack(house_index, houses, used_names, used_housestyles, used_foods, used_vacations, used_heights, used_cigars):
        if house_index == 6:
            if check_all_constraints(houses):
                return houses
            else:
                return None
        
        current_house = houses[house_index]
        pre_filled = {}
        for attr in ['Name', 'HouseStyle', 'Food', 'Vacation', 'Height', 'Cigar']:
            if attr in current_house:
                pre_filled[attr] = current_house[attr]
        
        if len(pre_filled) > 0:
            for attr, value in pre_filled.items():
                if attr == 'Name' and value in used_names:
                    return None
                elif attr == 'HouseStyle' and value in used_housestyles:
                    return None
                elif attr == 'Food' and value in used_foods:
                    return None
                elif attr == 'Vacation' and value in used_vacations:
                    return None
                elif attr == 'Height' and value in used_heights:
                    return None
                elif attr == 'Cigar' and value in used_cigars:
                    return None
            new_used_names = used_names | {pre_filled.get('Name', None)}
            new_used_housestyles = used_housestyles | {pre_filled.get('HouseStyle', None)}
            new_used_foods = used_foods | {pre_filled.get('Food', None)}
            new_used_vacations = used_vacations | {pre_filled.get('Vacation', None)}
            new_used_heights = used_heights | {pre_filled.get('Height', None)}
            new_used_cigars = used_cigars | {pre_filled.get('Cigar', None)}
            return backtrack(house_index + 1, houses, new_used_names, new_used_housestyles, new_used_foods, new_used_vacations, new_used_heights, new_used_cigars)
        
        for name in [n for n in names if n not in used_names]:
            for housestyle in [hs for hs in housestyles if hs not in used_housestyles]:
                for food in [f for f in foods if f not in used_foods]:
                    for vacation in [v for v in vacations if v not in used_vacations]:
                        for height in [h for h in heights if h not in used_heights]:
                            for cigar in [c for c in cigars if c not in used_cigars]:
                                temp_house = {
                                    'Name': name,
                                    'HouseStyle': housestyle,
                                    'Food': food,
                                    'Vacation': vacation,
                                    'Height': height,
                                    'Cigar': cigar
                                }
                                new_used_names = used_names | {name}
                                new_used_housestyles = used_housestyles | {housestyle}
                                new_used_foods = used_foods | {food}
                                new_used_vacations = used_vacations | {vacation}
                                new_used_heights = used_heights | {height}
                                new_used_cigars = used_cigars | {cigar}
                                houses[house_index] = temp_house.copy()
                                result = backtrack(house_index + 1, houses, new_used_names, new_used_housestyles, new_used_foods, new_used_vacations, new_used_heights, new_used_cigars)
                                if result is not None:
                                    return result
        return None

    # Initialize houses
    houses = [{} for _ in range(6)]
    houses[4]['Name'] = 'Alice'
    houses[4]['Food'] = 'spaghetti'
    houses[4]['HouseStyle'] = 'Victorian'
    houses[3]['Name'] = 'Eric'
    
    solution = backtrack(0, houses, set(), set(), set(), set(), set(), set())
    
    if solution is None:
        return None
    
    # Format the solution into the required JSON structure
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
            "rows": []
        }
    }
    for i in range(6):
        house_data = [
            str(i + 1),
            solution[i]['Name'],
            solution[i]['HouseStyle'],
            solution[i]['Food'],
            solution[i]['Vacation'],
            solution[i]['Height'],
            solution[i]['Cigar']
        ]
        result['solution']['rows'].append(house_data)
    
    return json.dumps(result, indent=2)

# Run the solver and print the result
print(solve_puzzle())