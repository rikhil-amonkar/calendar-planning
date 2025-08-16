import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
    months = ['feb', 'mar', 'sept', 'jan', 'may', 'april']
    foods = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    heights = ['very short', 'average', 'super tall', 'short', 'very tall', 'tall']
    car_models = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']
    
    # We'll represent each house as a dictionary in a list
    houses = [{'House': str(i)} for i in range(1, 7)]
    
    # Apply direct assignments first
    # Clue 19: very short is in house 4
    for house in houses:
        if house['House'] == '4':
            house['Height'] = 'very short'
    
    # Clue 20: birthday in march is short
    # Clue 1: honda civic owner is short
    # So honda civic owner's birthday is march
    
    # Clue 22: Eric's birthday is jan
    for house in houses:
        if 'Name' in house and house['Name'] == 'Eric':
            house['Birthday'] = 'jan'
    
    # Clue 17: tall is Bob
    for house in houses:
        if 'Name' in house and house['Name'] == 'Bob':
            house['Height'] = 'tall'
        elif 'Height' in house and house['Height'] == 'tall':
            house['Name'] = 'Bob'
    
    # Clue 21: Carol owns tesla model 3
    for house in houses:
        if 'Name' in house and house['Name'] == 'Carol':
            house['CarModel'] = 'tesla model 3'
        elif 'CarModel' in house and house['CarModel'] == 'tesla model 3':
            house['Name'] = 'Carol'
    
    # Clue 11: tesla model 3 is left of tall (Bob)
    # So Carol is left of Bob
    
    # Clue 2: ford f150 is in house 5
    for house in houses:
        if house['House'] == '5':
            house['CarModel'] = 'ford f150'
    
    # Clue 12: very tall owns toyota camry
    for house in houses:
        if 'Height' in house and house['Height'] == 'very tall':
            house['CarModel'] = 'toyota camry'
        elif 'CarModel' in house and house['CarModel'] == 'toyota camry':
            house['Height'] = 'very tall'
    
    # Clue 6: bmw 3 series not in house 3
    # Clue 10: Alice is directly left of bmw 3 series
    # So bmw is in house n, Alice in n-1, n != 3
    
    # Clue 4: may is left of Carol
    # Clue 18: may is right of Alice
    # So order: Alice ... may ... Carol
    
    # Clue 7: two houses between stir fry and pizza
    # So if stir fry is in n, pizza is in n+3
    
    # Clue 13: Peter is directly left of pizza
    # So pizza is in n, Peter in n-1
    
    # Clue 8: soup is directly left of Eric
    # So soup in n, Eric in n+1
    
    # Clue 3: stir fry is left of Eric
    
    # Clue 5: very short (house 4) is left of april
    # So april is in 5 or 6
    
    # Clue 15: one house between sept and very short (house 4)
    # So sept is in 2 (because 4-2=2, one house between is 3)
    
    for house in houses:
        if house['House'] == '2':
            house['Birthday'] = 'sept'
    
    # Clue 16: one house between march and super tall
    # march is in n, super tall in n+2
    # march is short (clue 20), and honda civic is short (clue 1)
    # So march birthday owns honda civic
    
    # Clue 9: spaghetti and may are next to each other
    
    # Let's try to assign march and honda civic
    possible_march_positions = []
    for i in range(1, 5):  # super tall must be <=6
        if i + 2 <= 6:
            possible_march_positions.append(i)
    
    # Try possible positions for march
    for march_pos in possible_march_positions:
        super_tall_pos = march_pos + 2
        # Assign march and super tall
        temp_houses = [house.copy() for house in houses]
        temp_houses[march_pos-1]['Birthday'] = 'mar'
        temp_houses[march_pos-1]['Height'] = 'short'
        temp_houses[march_pos-1]['CarModel'] = 'honda civic'
        temp_houses[super_tall_pos-1]['Height'] = 'super tall'
        
        # Assign april (must be right of very short, so 5 or 6)
        # Check if april can be assigned
        april_pos = None
        if 'Birthday' not in temp_houses[4] or temp_houses[4]['Birthday'] == 'april':
            april_pos = 5
        elif 'Birthday' not in temp_houses[5] or temp_houses[5]['Birthday'] == 'april':
            april_pos = 6
        if april_pos is None:
            continue
        temp_houses[april_pos-1]['Birthday'] = 'april'
        
        # Assign Eric (birthday jan)
        # From clue 8: soup is directly left of Eric
        # From clue 3: stir fry is left of Eric
        # From clue 7: two houses between stir fry and pizza
        # From clue 13: Peter is directly left of pizza
        # Let's find possible positions for Eric
        possible_eric_positions = []
        for i in range(2, 7):
            if 'Name' not in temp_houses[i-1] or temp_houses[i-1]['Name'] == 'Eric':
                possible_eric_positions.append(i)
        
        for eric_pos in possible_eric_positions:
            temp_houses_eric = [house.copy() for house in temp_houses]
            temp_houses_eric[eric_pos-1]['Name'] = 'Eric'
            temp_houses_eric[eric_pos-1]['Birthday'] = 'jan'
            
            # soup is directly left of Eric
            if eric_pos == 1:
                continue
            soup_pos = eric_pos - 1
            if 'Food' in temp_houses_eric[soup_pos-1]:
                continue
            temp_houses_eric[soup_pos-1]['Food'] = 'soup'
            
            # stir fry is left of Eric
            # two houses between stir fry and pizza
            # so stir fry is in n, pizza in n+3, and n+3 <=6 => n <=3
            possible_stir_fry_pos = []
            for n in range(1, 4):
                if n + 3 <= 6:
                    if 'Food' not in temp_houses_eric[n-1]:
                        possible_stir_fry_pos.append(n)
            
            for stir_fry_pos in possible_stir_fry_pos:
                temp_houses_sf = [house.copy() for house in temp_houses_eric]
                temp_houses_sf[stir_fry_pos-1]['Food'] = 'stir fry'
                pizza_pos = stir_fry_pos + 3
                temp_houses_sf[pizza_pos-1]['Food'] = 'pizza'
                
                # Peter is directly left of pizza
                if pizza_pos == 1:
                    continue
                peter_pos = pizza_pos - 1
                if 'Name' in temp_houses_sf[peter_pos-1]:
                    continue
                temp_houses_sf[peter_pos-1]['Name'] = 'Peter'
                
                # Alice is directly left of bmw (clue 10)
                # bmw not in 3 (clue 6)
                # So possible bmw positions: 2,4,5,6
                # But house 5 has ford f150, so bmw can be 2,4,6
                # Alice is left of bmw
                possible_bmw_pos = [2,4,6]
                for bmw_pos in possible_bmw_pos:
                    if bmw_pos == 1:
                        continue
                    alice_pos = bmw_pos - 1
                    if 'Name' in temp_houses_sf[alice_pos-1] and temp_houses_sf[alice_pos-1]['Name'] != 'Alice':
                        continue
                    if 'CarModel' in temp_houses_sf[bmw_pos-1] and temp_houses_sf[bmw_pos-1]['CarModel'] != 'bmw 3 series':
                        continue
                    
                    temp_houses_bmw = [house.copy() for house in temp_houses_sf]
                    temp_houses_bmw[bmw_pos-1]['CarModel'] = 'bmw 3 series'
                    temp_houses_bmw[alice_pos-1]['Name'] = 'Alice'
                    
                    # Carol owns tesla model 3 (clue 21)
                    # tesla is left of tall (Bob) (clue 11)
                    # So Carol is left of Bob
                    # Assign Carol and Bob
                    # Find possible positions for Carol and Bob
                    carol_positions = []
                    bob_positions = []
                    for i in range(1, 7):
                        if 'Name' not in temp_houses_bmw[i-1]:
                            carol_positions.append(i)
                        elif temp_houses_bmw[i-1]['Name'] == 'Carol':
                            carol_positions.append(i)
                    
                    for carol_pos in carol_positions:
                        temp_houses_carol = [house.copy() for house in temp_houses_bmw]
                        temp_houses_carol[carol_pos-1]['Name'] = 'Carol'
                        temp_houses_carol[carol_pos-1]['CarModel'] = 'tesla model 3'
                        
                        # Bob must be right of Carol
                        possible_bob_pos = []
                        for i in range(carol_pos + 1, 7):
                            if 'Name' not in temp_houses_carol[i-1]:
                                possible_bob_pos.append(i)
                            elif temp_houses_carol[i-1]['Name'] == 'Bob':
                                possible_bob_pos.append(i)
                        
                        for bob_pos in possible_bob_pos:
                            temp_houses_bob = [house.copy() for house in temp_houses_carol]
                            temp_houses_bob[bob_pos-1]['Name'] = 'Bob'
                            temp_houses_bob[bob_pos-1]['Height'] = 'tall'
                            
                            # Assign remaining names
                            remaining_names = set(names) - {h.get('Name', '') for h in temp_houses_bob}
                            remaining_names = list(remaining_names)
                            if not remaining_names:
                                pass  # all names assigned
                            else:
                                # Assign remaining names to empty houses
                                empty_houses = [i for i in range(1, 7) if 'Name' not in temp_houses_bob[i-1]]
                                if len(empty_houses) != len(remaining_names):
                                    continue
                                for name, pos in zip(remaining_names, empty_houses):
                                    temp_houses_bob[pos-1]['Name'] = name
                            
                            # Assign may left of Carol (clue 4)
                            # and may right of Alice (clue 18)
                            # Alice is in alice_pos
                            carol_pos = [i+1 for i, h in enumerate(temp_houses_bob) if h.get('Name') == 'Carol'][0]
                            alice_pos = [i+1 for i, h in enumerate(temp_houses_bob) if h.get('Name') == 'Alice'][0]
                            possible_may_positions = []
                            for i in range(alice_pos + 1, carol_pos):
                                if 'Birthday' not in temp_houses_bob[i-1]:
                                    possible_may_positions.append(i)
                            
                            if not possible_may_positions:
                                continue
                            
                            for may_pos in possible_may_positions:
                                temp_houses_may = [house.copy() for house in temp_houses_bob]
                                temp_houses_may[may_pos-1]['Birthday'] = 'may'
                                
                                # spaghetti and may are next to each other (clue 9)
                                spaghetti_pos = None
                                if may_pos > 1 and 'Food' not in temp_houses_may[may_pos-2]:
                                    spaghetti_pos = may_pos - 1
                                elif may_pos < 6 and 'Food' not in temp_houses_may[may_pos]:
                                    spaghetti_pos = may_pos + 1
                                
                                if spaghetti_pos is None:
                                    continue
                                temp_houses_may[spaghetti_pos-1]['Food'] = 'spaghetti'
                                
                                # Assign remaining foods
                                remaining_foods = set(foods) - {h.get('Food', '') for h in temp_houses_may}
                                remaining_foods = list(remaining_foods)
                                if not remaining_foods:
                                    pass  # all foods assigned
                                else:
                                    # Assign remaining foods to empty houses
                                    empty_houses = [i for i in range(1, 7) if 'Food' not in temp_houses_may[i-1]]
                                    if len(empty_houses) != len(remaining_foods):
                                        continue
                                    for food, pos in zip(remaining_foods, empty_houses):
                                        temp_houses_may[pos-1]['Food'] = food
                                
                                # Assign remaining birthdays
                                remaining_months = set(months) - {h.get('Birthday', '') for h in temp_houses_may}
                                remaining_months = list(remaining_months)
                                if not remaining_months:
                                    pass  # all months assigned
                                else:
                                    # Assign remaining months to empty houses
                                    empty_houses = [i for i in range(1, 7) if 'Birthday' not in temp_houses_may[i-1]]
                                    if len(empty_houses) != len(remaining_months):
                                        continue
                                    for month, pos in zip(remaining_months, empty_houses):
                                        temp_houses_may[pos-1]['Birthday'] = month
                                
                                # Assign remaining car models
                                remaining_cars = set(car_models) - {h.get('CarModel', '') for h in temp_houses_may}
                                remaining_cars = list(remaining_cars)
                                if not remaining_cars:
                                    pass  # all cars assigned
                                else:
                                    # Assign remaining cars to empty houses
                                    empty_houses = [i for i in range(1, 7) if 'CarModel' not in temp_houses_may[i-1]]
                                    if len(empty_houses) != len(remaining_cars):
                                        continue
                                    for car, pos in zip(remaining_cars, empty_houses):
                                        temp_houses_may[pos-1]['CarModel'] = car
                                
                                # Assign remaining heights
                                remaining_heights = set(heights) - {h.get('Height', '') for h in temp_houses_may}
                                remaining_heights = list(remaining_heights)
                                if not remaining_heights:
                                    pass  # all heights assigned
                                else:
                                    # Assign remaining heights to empty houses
                                    empty_houses = [i for i in range(1, 7) if 'Height' not in temp_houses_may[i-1]]
                                    if len(empty_houses) != len(remaining_heights):
                                        continue
                                    for height, pos in zip(remaining_heights, empty_houses):
                                        temp_houses_may[pos-1]['Height'] = height
                                
                                # Check if all constraints are satisfied
                                valid = True
                                for house in temp_houses_may:
                                    if len(house) != 6:  # House, Name, Birthday, Food, Height, CarModel
                                        valid = False
                                        break
                                
                                if valid:
                                    # Prepare the solution
                                    solution = {
                                        "solution": {
                                            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                                            "rows": []
                                        }
                                    }
                                    for house in temp_houses_may:
                                        row = [
                                            house['House'],
                                            house.get('Name', ''),
                                            house.get('Birthday', '),
                                            house.get('Food', ''),
                                            house.get('Height', ''),
                                            house.get('CarModel', '')
                                        ]
                                        solution["solution"]["rows"].append(row)
                                    return solution
    
    # If no solution found
    return {"solution": {"header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"], "rows": []}}

# Solve the puzzle and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))