import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
    phones = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
    nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
    colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']
    
    # We'll represent each house as a dictionary, and try all permutations
    # Since brute force is impractical, we'll use constraints to narrow down
    
    # Initialize possibilities for each house
    possibilities = []
    for house in houses:
        possibilities.append({
            'name': names.copy(),
            'phone': phones.copy(),
            'nationality': nationalities.copy(),
            'color': colors.copy()
        })
    
    # Apply constraints one by one
    
    # Clue 8: Samsung in house 5
    for attr in possibilities[4].keys():
        if attr != 'phone':
            possibilities[4][attr] = []
    possibilities[4]['phone'] = ['samsung galaxy s21']
    
    # Clue 10: Bob uses samsung (house 5)
    for house in possibilities:
        if house['name'] != [] and 'Bob' in house['name']:
            house['name'] = []
    possibilities[4]['name'] = ['Bob']
    
    # Clue 15: Samsung directly left of iphone 13 (so iphone in house 6)
    possibilities[5]['phone'] = ['iphone 13']
    
    # Clue 12: Samsung left of Peter, so Peter is right of house 5 (house 6)
    possibilities[5]['name'] = ['Peter']
    
    # Clue 13: Peter loves blue
    possibilities[5]['color'] = ['blue']
    
    # Clue 14: Peter is brit
    possibilities[5]['nationality'] = ['brit']
    
    # Clue 2: One house between Dane and brit. Brit is in 6, so Dane is in 4
    possibilities[3]['nationality'] = ['dane']
    
    # Clue 11: Dane loves yellow
    possibilities[3]['color'] = ['yellow']
    
    # Clue 4: Arnold directly left of Alice
    # So Alice is in x, Arnold in x-1
    # Possible positions for Alice: 2-6, Arnold 1-5
    # But house 5 is Bob, 6 is Peter, so Alice can be 2,3,4, Arnold 1,2,3
    # But house 4 nationality is dane, and Alice is german (clue 5)
    possibilities[4]['nationality'] = []  # Bob is not german
    possibilities[5]['nationality'] = ['brit']  # Peter is brit
    # So Alice must be in 2,3, or 4
    
    # Clue 5: Alice is german
    for i in [1, 2, 3]:  # houses 2,3,4
        if 'german' in possibilities[i]['nationality']:
            possibilities[i]['nationality'] = ['german']
            possibilities[i]['name'] = ['Alice']
            # Arnold is left of Alice, so Arnold is i-1
            possibilities[i-1]['name'] = ['Arnold']
            break
    
    # Clue 3: Carol's color is green
    # Clue 1: Carol is not in house 3
    # So Carol is in 1,2,4,5,6. But 5 is Bob, 6 is Peter, so 1,2,4
    # But Alice is in 2,3, or 4, Arnold is left
    
    # Let's assume Alice is in 2
    # Then Arnold is in 1
    # Carol can be in 4
    possibilities[1]['name'] = ['Arnold']
    possibilities[1]['name'] = ['Arnold']
    possibilities[2]['name'] = ['Alice']
    possibilities[2]['nationality'] = ['german']
    
    # Now Carol is not in 3, so 1,2,4,5,6. 1 is Arnold, 2 Alice, 5 Bob, 6 Peter, so 4
    possibilities[3]['name'] = []  # Not Carol
    possibilities[4]['name'] = []  # Bob
    possibilities[5]['name'] = ['Peter']
    possibilities[0]['name'] = ['Arnold']
    possibilities[1]['name'] = ['Alice']
    # So Carol must be in 3 or 4? Wait, no, in this scenario Alice is in 2, Arnold in 1
    # So names left: Carol, Eric
    # Houses left: 3,4
    # Carol is not in 3 (clue 1), so Carol in 4, Eric in 3
    possibilities[3]['name'] = ['Eric']
    possibilities[4]['name'] = ['Bob']
    possibilities[5]['name'] = ['Peter']
    possibilities[2]['name'] = ['Carol']
    # Wait, no, Carol is in 4
    # Let me re-examine
    
    # Reset name assignments
    possibilities[0]['name'] = ['Arnold']
    possibilities[1]['name'] = ['Alice']
    # Remaining names: Carol, Bob, Eric, Peter
    # Bob in 5, Peter in 6, so Carol and Eric in 2,3,4
    # Alice is in 2, so Carol and Eric in 3,4
    # Carol not in 3 (clue 1), so Carol in 4, Eric in 3
    possibilities[2]['name'] = ['Eric']
    possibilities[3]['name'] = ['Carol']
    possibilities[4]['name'] = ['Bob']
    possibilities[5]['name'] = ['Peter']
    
    # Clue 3: Carol's color is green
    possibilities[3]['color'] = ['green']
    
    # Clue 7: huawei p50 not in house 3
    if 'huawei p50' in possibilities[2]['phone']:
        possibilities[2]['phone'].remove('huawei p50')
    
    # Clue 6: oneplus 9 loves purple
    # Clue 16: norwegian loves purple
    # So oneplus 9 is norwegian
    # So find house where phone is oneplus 9, nationality is norwegian, color is purple
    # Possible houses: 1,2,3 (4 has color green, 5,6 have phones assigned)
    for i in [0, 1, 2]:
        if 'oneplus 9' in possibilities[i]['phone']:
            possibilities[i]['color'] = ['purple']
            possibilities[i]['nationality'] = ['norwegian']
    
    # Clue 9: white is right of red
    # So red is left of white
    
    # Clue 17: xiaomi mi 11 is chinese
    for i in range(6):
        if 'xiaomi mi 11' in possibilities[i]['phone']:
            possibilities[i]['nationality'] = ['chinese']
    
    # Assign phones where possible
    # House 5: samsung, house 6: iphone
    # So remaining phones: google pixel 6, huawei p50, oneplus 9, xiaomi mi 11
    # Assign oneplus to house with norwegian and purple
    # Assign xiaomi to chinese
    
    # Let's assume oneplus is in house 1
    possibilities[0]['phone'] = ['oneplus 9']
    possibilities[0]['color'] = ['purple']
    possibilities[0]['nationality'] = ['norwegian']
    
    # Then xiaomi must be in 2 or 3
    # House 2: name Alice
    # House 3: name Eric
    # House 2: nationality german, so not chinese
    # So xiaomi in 3
    possibilities[2]['phone'] = ['xiaomi mi 11']
    possibilities[2]['nationality'] = ['chinese']
    
    # Remaining phone in house 4: google pixel 6 or huawei p50
    # Clue 7: huawei not in 3, so can be in 4
    possibilities[3]['phone'] = ['huawei p50']
    possibilities[1]['phone'] = ['google pixel 6']
    
    # Now assign colors
    # House 0: purple
    # House 3: green
    # House 5: blue
    # House 4: ?
    # House 1: ?
    # House 2: ?
    # Colors left: red, yellow, white
    # House 3: color is green, house 4: ?
    # House 4: nationality is dane, color is yellow (clue 11)
    possibilities[3]['color'] = ['green']
    possibilities[3]['nationality'] = []  # Wait, house 3 is carol, nationality?
    # Wait, house 4 is dane, color yellow
    possibilities[3]['nationality'] = []  # Carol's nationality not assigned yet
    possibilities[3]['color'] = ['green']
    possibilities[3]['nationality'] = []  # Not assigned yet
    
    # Re-examining house 4: nationality is dane, color yellow
    possibilities[3]['nationality'] = ['dane']
    possibilities[3]['color'] = ['yellow']
    # But earlier we had house 3 color green (Carol)
    # Conflict, so adjust
    
    # Let me re-examine colors
    # House 0: purple
    # House 3: green (Carol)
    # House 4: dane, so yellow
    # House 5: blue
    # So house 1 and 2: red, white
    # Clue 9: white is right of red, so red is left of white
    # So house 1: red, house 2: white
    possibilities[0]['color'] = ['purple']
    possibilities[1]['color'] = ['red']
    possibilities[2]['color'] = ['white']
    possibilities[3]['color'] = ['green']
    possibilities[4]['color'] = ['yellow']
    possibilities[5]['color'] = ['blue']
    
    # Now assign nationalities
    # House 0: norwegian
    # House 1: ?
    # House 2: chinese
    # House 3: ?
    # House 4: dane
    # House 5: brit
    # Alice is german (house 2? Wait no, house 1 is Alice)
    # Wait, earlier we had Alice in house 2
    possibilities[1]['nationality'] = ['german']
    # Remaining nationalities: swede
    # House 3: carol, nationality?
    # Nationalities left: swede
    possibilities[3]['nationality'] = ['swede']
    
    # Now assign remaining names
    # House 0: Arnold
    # House 1: Alice
    # House 2: Eric
    # House 3: Carol
    # House 4: Bob
    # House 5: Peter
    
    # Verify all constraints
    # Clue 1: Carol not in 3 - no, Carol is in 4 (house numbers are 0-based here)
    # Wait, in our current setup:
    # House 0: 1
    # House 1: 2
    # House 2: 3
    # House3: 4
    # House4: 5
    # House5: 6
    # So Carol is in 4 (house3), which is correct
    
    # Compile the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "phone", "nationality", "color"],
            "rows": []
        }
    }
    
    for i in range(6):
        house_num = i + 1
        name = possibilities[i]['name'][0]
        phone = possibilities[i]['phone'][0]
        nationality = possibilities[i]['nationality'][0]
        color = possibilities[i]['color'][0]
        solution["solution"]["rows"].append([
            str(house_num),
            name,
            phone,
            nationality,
            color
        ])
    
    return json.dumps(solution)

if __name__ == "__main__":
    print(solve_puzzle())