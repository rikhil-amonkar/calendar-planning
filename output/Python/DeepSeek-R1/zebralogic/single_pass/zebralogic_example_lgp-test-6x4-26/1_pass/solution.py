import json

def find_index(houses, attr, value):
    for i, house in enumerate(houses):
        if house[attr] == value:
            return i
    return -1

def satisfies_all_constraints(houses):
    # Clue 1: Hamster right of March
    idx_mar = find_index(houses, 'month', 'mar')
    idx_ham = find_index(houses, 'pet', 'hamster')
    if idx_mar == -1 or idx_ham == -1 or idx_ham <= idx_mar:
        return False

    # Clue 2: January left of September
    idx_jan = find_index(houses, 'month', 'jan')
    idx_sept = find_index(houses, 'month', 'sept')
    if idx_jan == -1 or idx_sept == -1 or idx_jan >= idx_sept:
        return False

    # Clue 3: May in second house
    if houses[1]['month'] != 'may':
        return False

    # Clue 4: Colonial in second house
    if houses[1]['house_style'] != 'colonial':
        return False

    # Clue 5: Carol in third house
    if houses[2]['name'] != 'Carol':
        return False

    # Clue 6: Mediterranean not in sixth house
    if houses[5]['house_style'] == 'mediterranean':
        return False

    # Clue 7: Fish right of Bob
    idx_bob = find_index(houses, 'name', 'Bob')
    idx_fish = find_index(houses, 'pet', 'fish')
    if idx_bob == -1 or idx_fish == -1 or idx_fish <= idx_bob:
        return False

    # Clue 8: Eric in sixth house
    if houses[5]['name'] != 'Eric':
        return False

    # Clue 9: One house between cat and Victorian
    idx_cat = find_index(houses, 'pet', 'cat')
    idx_vic = find_index(houses, 'house_style', 'victorian')
    if idx_cat == -1 or idx_vic == -1 or abs(idx_cat - idx_vic) != 2:
        return False

    # Clue 10: Two houses between Victorian and hamster
    if abs(idx_vic - idx_ham) != 3:
        return False

    # Clue 11: Craftsman is Arnold
    idx_craftsman = find_index(houses, 'house_style', 'craftsman')
    if idx_craftsman == -1 or houses[idx_craftsman]['name'] != 'Arnold':
        return False

    # Clue 12: Colonial left of Modern
    idx_modern = find_index(houses, 'house_style', 'modern')
    if idx_modern == -1 or idx_modern <= 1:
        return False

    # Clue 13: Fish not in second house
    if houses[1]['pet'] == 'fish':
        return False

    # Clue 14: Peter in colonial (already set)

    # Clue 15: January directly left of April
    idx_april = find_index(houses, 'month', 'april')
    if idx_jan == -1 or idx_april == -1 or idx_jan + 1 != idx_april:
        return False

    # Clue 16: One house between bird and Modern
    idx_bird = find_index(houses, 'pet', 'bird')
    if idx_bird == -1 or idx_modern == -1 or abs(idx_bird - idx_modern) != 2:
        return False

    # Clue 17: Carol's birthday in March
    if houses[2]['month'] != 'mar':
        return False

    # Clue 18: Craftsman in fourth house
    if houses[3]['house_style'] != 'craftsman':
        return False

    # Clue 19: Dog in fourth house
    if houses[3]['pet'] != 'dog':
        return False

    return True

def main():
    houses = [
        {'name': None, 'pet': None, 'house_style': None, 'month': None},
        {'name': 'Peter', 'pet': None, 'house_style': 'colonial', 'month': 'may'},
        {'name': 'Carol', 'pet': None, 'house_style': None, 'month': 'mar'},
        {'name': 'Arnold', 'pet': 'dog', 'house_style': 'craftsman', 'month': None},
        {'name': None, 'pet': None, 'house_style': None, 'month': None},
        {'name': 'Eric', 'pet': None, 'house_style': None, 'month': None}
    ]
    
    available_names = ['Bob', 'Alice']
    available_pets = ['bird', 'cat', 'rabbit', 'fish', 'hamster']
    available_house_styles = ['victorian', 'ranch', 'modern', 'mediterranean']
    available_months = ['sept', 'feb', 'jan', 'april']
    
    for name0 in available_names:
        houses[0]['name'] = name0
        for pet0 in available_pets:
            houses[0]['pet'] = pet0
            for house_style0 in available_house_styles:
                houses[0]['house_style'] = house_style0
                for month0 in available_months:
                    houses[0]['month'] = month0
                    
                    available_pets1 = [p for p in available_pets if p != pet0]
                    for pet1 in available_pets1:
                        houses[1]['pet'] = pet1
                        
                        available_house_styles2 = [hs for hs in available_house_styles if hs != house_style0]
                        available_pets2 = [p for p in available_pets1 if p != pet1]
                        for house_style2 in available_house_styles2:
                            houses[2]['house_style'] = house_style2
                            for pet2 in available_pets2:
                                houses[2]['pet'] = pet2
                                
                                available_months3 = [m for m in available_months if m != month0]
                                for month3 in available_months3:
                                    houses[3]['month'] = month3
                                    
                                    available_names4 = [n for n in available_names if n != name0]
                                    if len(available_names4) != 1:
                                        continue
                                    name4 = available_names4[0]
                                    houses[4]['name'] = name4
                                    
                                    available_house_styles4 = [hs for hs in available_house_styles2 if hs != house_style2]
                                    available_pets4 = [p for p in available_pets2 if p != pet2]
                                    available_months4 = [m for m in available_months3 if m != month3]
                                    for house_style4 in available_house_styles4:
                                        houses[4]['house_style'] = house_style4
                                        for pet4 in available_pets4:
                                            houses[4]['pet'] = pet4
                                            for month4 in available_months4:
                                                houses[4]['month'] = month4
                                                
                                                available_pets5 = [p for p in available_pets4 if p != pet4]
                                                available_house_styles5 = [hs for hs in available_house_styles4 if hs != house_style4]
                                                available_months5 = [m for m in available_months4 if m != month4]
                                                if len(available_pets5) != 1 or len(available_house_styles5) != 1 or len(available_months5) != 1:
                                                    continue
                                                pet5 = available_pets5[0]
                                                house_style5 = available_house_styles5[0]
                                                month5 = available_months5[0]
                                                houses[5]['pet'] = pet5
                                                houses[5]['house_style'] = house_style5
                                                houses[5]['month'] = month5
                                                
                                                if satisfies_all_constraints(houses):
                                                    solution = {
                                                        "header": ["House", "Name", "Pet", "House Style", "Birthday Month"],
                                                        "rows": []
                                                    }
                                                    for i in range(6):
                                                        row = [
                                                            str(i+1),
                                                            houses[i]['name'],
                                                            houses[i]['pet'],
                                                            houses[i]['house_style'],
                                                            houses[i]['month']
                                                        ]
                                                        solution['rows'].append(row)
                                                    print(json.dumps({"solution": solution}))
                                                    return
    
    print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()