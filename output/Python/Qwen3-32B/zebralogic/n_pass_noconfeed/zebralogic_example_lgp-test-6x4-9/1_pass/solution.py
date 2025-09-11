import json

# Define the possible values
names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
phone_models = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']

# Initialize houses with known values
houses = [
    {'House': 1, 'Name': None, 'PhoneModel': None, 'Nationality': None, 'Color': None},
    {'House': 2, 'Name': None, 'PhoneModel': None, 'Nationality': None, 'Color': None},
    {'House': 3, 'Name': None, 'PhoneModel': None, 'Nationality': None, 'Color': None},
    {'House': 4, 'Name': None, 'PhoneModel': None, 'Nationality': 'dane', 'Color': 'yellow'},
    {'House': 5, 'Name': 'Bob', 'PhoneModel': 'samsung galaxy s21', 'Nationality': None, 'Color': None},
    {'House': 6, 'Name': 'Peter', 'PhoneModel': 'iphone 13', 'Nationality': 'brit', 'Color': 'blue'},
]

# Possible Arnold and Alice positions: (arnold_house, alice_house)
possible_positions = [(0, 1), (1, 2)]  # (house 1-2, house 2-3)

def solve():
    for arnold_house, alice_house in possible_positions:
        # Check if these positions are available
        if houses[arnold_house]['Name'] is not None or houses[alice_house]['Name'] is not None:
            continue
        # Assign Arnold and Alice
        houses[arnold_house]['Name'] = 'Arnold'
        houses[alice_house]['Name'] = 'Alice'
        houses[alice_house]['Nationality'] = 'german'
        
        # Remaining nationalities to assign: swede, chinese, norwegian
        # They are for houses: [0, 1, 4] if arnold_house is 1, alice_house is 2
        # Need to determine which houses are available
        # The houses that need nationalities are those not yet assigned
        # For this example, let's assume the remaining are houses 0, arnold_house, 4
        # But this depends on the specific positions
        # For simplicity, let's proceed with the known scenario where arnold_house is 1 (house 2), alice_house is 2 (house 3)
        # In this case, the remaining houses for nationalities are 0 (house 1), 1 (house 2), 4 (house 5)
        # The nationalities to assign are swede, chinese, norwegian
        
        # Try assigning Norwegian to house 0 (house 1)
        houses[0]['Nationality'] = 'norwegian'
        houses[0]['PhoneModel'] = 'oneplus 9'
        houses[0]['Color'] = 'purple'
        
        # Remaining nationalities: chinese and swede for houses 1 and 4
        # Assign chinese to house 1 (house 2)
        houses[1]['Nationality'] = 'chinese'
        houses[1]['PhoneModel'] = 'xiaomi mi 11'
        
        # Assign swede to house 4 (house 5)
        houses[4]['Nationality'] = 'swede'
        
        # Assign remaining phone models: google pixel 6 and huawei p50 to houses 2 and 3 (house 3 and 4)
        # House 2 (index 2, house 3) and house 3 (index 3, house 4)
        # Clue 7: huawei p50 not in house 3 (index 2)
        # So house 2's phone is google pixel 6, house 3's is huawei p50
        houses[2]['PhoneModel'] = 'google pixel 6'
        houses[3]['PhoneModel'] = 'huawei p50'
        
        # Assign colors: remaining are red, green, white for houses 1, 2, 4 (house 2, 3, 5)
        # Carol's color is green. She must be in house 3 (index 3, house 4), since house 0 is purple, house 3 is yellow, house 5 is blue
        # Assign house 3's color to green
        houses[3]['Color'] = 'green'
        
        # Remaining colors for house 1 (house 2) and house 2 (house 3) are red and white
        # Clue 9: white is to the right of red
        # Assign house 1 (house 2) to red, house 2 (house 3) to white
        houses[1]['Color'] = 'red'
        houses[2]['Color'] = 'white'
        
        # Assign names for houses 0 and 3 (index 0 and 3)
        # The remaining names are Carol and Eric
        # Since house 3 (index 3) has color green, it must be Carol
        houses[3]['Name'] = 'Carol'
        houses[0]['Name'] = 'Eric'
        
        # Check all constraints
        if check_all_constraints():
            return houses
        else:
            # backtrack
            houses[3]['Name'] = None
            houses[0]['Name'] = None
            houses[1]['Color'] = None
            houses[2]['Color'] = None
            houses[3]['Color'] = None
            houses[2]['PhoneModel'] = None
            houses[3]['PhoneModel'] = None
            houses[4]['Nationality'] = None
            houses[1]['PhoneModel'] = None
            houses[1]['Nationality'] = None
            houses[0]['Nationality'] = None
            houses[0]['PhoneModel'] = None
            houses[0]['Color'] = None
            houses[alice_house]['Nationality'] = None
            houses[arnold_house]['Name'] = None
            houses[alice_house]['Name'] = None
    return None

def check_all_constraints():
    # Check all clues
    # Clue 1: Carol is not in third house (house 3)
    if houses[2]['Name'] == 'Carol':
        return False
    # Clue 2: one house between Dane and Brit
    dane_house = next(i for i, h in enumerate(houses) if h['Nationality'] == 'dane')
    brit_house = next(i for i, h in enumerate(houses) if h['Nationality'] == 'brit')
    if abs(dane_house - brit_house) != 2:
        return False
    # Clue 3: Carol's color is green
    if any(h['Name'] == 'Carol' and h['Color'] != 'green' for h in houses):
        return False
    # Clue 4: Arnold directly left of Alice
    arnold_house = next(i for i, h in enumerate(houses) if h['Name'] == 'Arnold')
    alice_house = next(i for i, h in enumerate(houses) if h['Name'] == 'Alice')
    if alice_house != arnold_house + 1:
        return False
    # Clue 5: Alice is German
    if any(h['Name'] == 'Alice' and h['Nationality'] != 'german' for h in houses):
        return False
    # Clue 6: OnePlus 9 loves purple
    for h in houses:
        if h['PhoneModel'] == 'oneplus 9' and h['Color'] != 'purple':
            return False
    # Clue 7: Huawei p50 not in third house (index 2)
    if houses[2]['PhoneModel'] == 'huawei p50':
        return False
    # Clue 8: Samsung in house 5
    if houses[4]['PhoneModel'] != 'samsung galaxy s21':
        return False
    # Clue 9: white is to the right of red
    red_house = next((i for i, h in enumerate(houses) if h['Color'] == 'red'), None)
    white_house = next((i for i, h in enumerate(houses) if h['Color'] == 'white'), None)
    if red_house is not None and white_house is not None and white_house < red_house:
        return False
    # Clue 10: Samsung user is Bob
    if any(h['PhoneModel'] == 'samsung galaxy s21' and h['Name'] != 'Bob' for h in houses):
        return False
    # Clue 11: Dane loves yellow
    if any(h['Nationality'] == 'dane' and h['Color'] != 'yellow' for h in houses):
        return False
    # Clue 12: Samsung is left of Peter
    samsung_house = next(i for i, h in enumerate(houses) if h['PhoneModel'] == 'samsung galaxy s21')
    peter_house = next(i for i, h in enumerate(houses) if h['Name'] == 'Peter')
    if peter_house <= samsung_house:
        return False
    # Clue 13: Peter loves blue
    if any(h['Name'] == 'Peter' and h['Color'] != 'blue' for h in houses):
        return False
    # Clue 14: Peter is Brit
    if any(h['Name'] == 'Peter' and h['Nationality'] != 'brit' for h in houses):
        return False
    # Clue 15: Samsung directly left of iPhone
    if houses[4]['PhoneModel'] == 'samsung galaxy s21' and houses[5]['PhoneModel'] != 'iphone 13':
        return False
    # Clue 16: Norwegian loves purple
    if any(h['Nationality'] == 'norwegian' and h['Color'] != 'purple' for h in houses):
        return False
    # Clue 17: Xiaomi Mi 11 is Chinese
    if any(h['PhoneModel'] == 'xiaomi mi 11' and h['Nationality'] != 'chinese' for h in houses):
        return False
    return True

solution = solve()
if solution:
    # Prepare the output
    output = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
            "rows": []
        }
    }
    for house in solution:
        row = [
            str(house['House']),
            house['Name'],
            house['PhoneModel'],
            house['Nationality'],
            house['Color']
        ]
        output['solution']['rows'].append(row)
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")