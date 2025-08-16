import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    # Preprocess clues to reduce search space
    # Clue 12: short is in house 6
    height_assignments = {6: 'short'}
    
    # Clue 4: Carol is very tall
    carol_height = 'very tall'
    
    # Clue 10: Carol uses xiaomi mi 11
    carol_phone = 'xiaomi mi 11'
    
    # Clue 9: super tall is in house 1
    height_assignments[1] = 'super tall'
    
    # Clue 8: tall is Arnold
    # So Arnold's height is tall
    
    # Clue 1: Bob is directly left of the person who is tall
    # So Bob is in house X, tall (Arnold) is in X+1
    
    # Clue 7: oneplus 9 is directly left of short (house 6)
    # So oneplus 9 is in house 5
    
    phone_assignments = {5: 'oneplus 9'}
    
    # Clue 5: one house between google pixel 6 and short (house 6)
    # So google pixel 6 is in house 4 (since short is 6, one between is 5)
    phone_assignments[4] = 'google pixel 6'
    
    # Clue 3: very short is right of google pixel 6 (house 4)
    # So very short is in 5 or 6, but 6 is short, so very short is 5
    height_assignments[5] = 'very short'
    
    # Clue 11: google pixel 6 (house 4) is right of Eric
    # So Eric is in house 1, 2, or 3
    
    # Clue 6: samsung galaxy s21 is not in house 1
    # So samsung is in 2,3,4,5,6. But 4 is google, 5 is oneplus, 6 is ?
    
    # Clue 2: Peter is left of iphone 13
    
    # Now assign remaining heights and phones
    remaining_heights = [h for h in heights if h not in height_assignments.values() and h != carol_height]
    remaining_phones = [p for p in phones if p not in phone_assignments.values() and p != carol_phone]
    
    # Assign Carol (must be in a house not yet assigned for height or phone)
    # Carol's height is very tall, phone is xiaomi mi 11
    # Possible houses: 2,3 (since 1 has super tall, 4,5,6 have assigned heights or phones)
    
    # Assign Arnold (height tall)
    # From clue 1: Bob is directly left of tall (Arnold)
    # So Arnold is in X+1, Bob is in X
    # Possible positions for Arnold: 2,3,4,5,6
    # But:
    # - 1: super tall
    # - 5: very short
    # - 6: short
    # So Arnold must be in 2,3, or 4 (height tall)
    # But house 4's height not assigned yet, but phone is google pixel 6
    # From clue 1: Bob is left of Arnold, so if Arnold is in 2, Bob in 1
    # But house 1 name not assigned yet
    
    # Try Arnold in 2 (height tall)
    # Then Bob is in 1
    # Carol must be in 3 (since her height is very tall, and house 3 height not assigned)
    # Assign Carol to house 3:
    name_assignments = {1: 'Bob', 2: 'Arnold', 3: 'Carol'}
    height_assignments[3] = 'very tall'
    phone_assignments[3] = 'xiaomi mi 11'
    
    # Now assign remaining names: Alice, Eric, Peter
    # From clue 11: Eric is left of google pixel 6 (house 4)
    # So Eric is in 1,2,3. But 1 is Bob, 2 is Arnold, so Eric must be in 3, but 3 is Carol
    # Contradiction, so Arnold cannot be in 2
    
    # Try Arnold in 3 (height tall)
    # Then Bob is in 2
    name_assignments = {2: 'Bob', 3: 'Arnold'}
    height_assignments[3] = 'tall'
    
    # Carol must be in house 1,2,4,5,6
    # 1: height super tall, not very tall
    # 2: name Bob, height not assigned
    # 4: phone google, height not assigned
    # 5: height very short
    # 6: height short
    # So Carol must be in 2 or 4 (very tall)
    # 2: name is Bob, so Carol must be in 4
    name_assignments[4] = 'Carol'
    height_assignments[4] = 'very tall'
    phone_assignments[4] = 'google pixel 6'  # But Carol's phone is xiaomi mi 11
    # Contradiction, so Carol cannot be in 4
    
    # Try Arnold in 4 (height tall)
    # Then Bob is in 3
    name_assignments = {3: 'Bob', 4: 'Arnold'}
    height_assignments[4] = 'tall'
    
    # Carol must be in 1,2,5,6
    # 1: height super tall
    # 5: very short
    # 6: short
    # So Carol must be in 2 (very tall)
    name_assignments[2] = 'Carol'
    height_assignments[2] = 'very tall'
    phone_assignments[2] = 'xiaomi mi 11'
    
    # From clue 11: google pixel 6 (house 4) is right of Eric
    # So Eric is left of 4: houses 1,2,3
    # 2 is Carol, so Eric is 1 or 3
    # 3 is Bob, so Eric is 1
    name_assignments[1] = 'Eric'
    
    # Remaining names: Alice, Peter
    # Houses left: 5,6
    name_assignments[5] = 'Alice'  # arbitrary, need to check clues
    name_assignments[6] = 'Peter'
    
    # Check clue 2: Peter is left of iphone 13
    # Peter is in 6, so iphone 13 must be to his right, but no house 7. Contradiction.
    # So swap Peter and Alice
    name_assignments[5] = 'Peter'
    name_assignments[6] = 'Alice'
    # Now Peter is left of iphone 13: iphone 13 must be to his right, so house 6
    phone_assignments[6] = 'iphone 13'
    
    # Assign remaining phones
    # Assigned phones: google pixel 6 (4), oneplus 9 (5), xiaomi mi 11 (2), iphone 13 (6)
    # Remaining phones: samsung galaxy s21, huawei p50
    # House 1 and 3 left
    # From clue 6: samsung not in 1, so samsung in 3
    phone_assignments[3] = 'samsung galaxy s21'
    phone_assignments[1] = 'huawei p50'
    
    # Assign remaining heights
    # Assigned heights: 1: super tall, 2: very tall, 3: ?, 4: tall, 5: very short, 6: short
    # Remaining heights: average
    height_assignments[3] = 'average'
    
    # Verify all clues
    # Clue 1: Bob (3) is directly left of tall (4) - yes
    # Clue 2: Peter (5) is left of iphone 13 (6) - yes
    # Clue 3: very short (5) is right of google pixel 6 (4) - yes
    # Clue 4: Carol is very tall (2) - yes
    # Clue 5: one house between google pixel 6 (4) and short (6) - yes (5)
    # Clue 6: samsung not in 1 - yes, in 3
    # Clue 7: oneplus 9 (5) directly left of short (6) - yes
    # Clue 8: tall is Arnold (4) - yes
    # Clue 9: super tall in 1 - yes
    # Clue 10: Carol uses xiaomi mi 11 (2) - yes
    # Clue 11: google pixel 6 (4) is right of Eric (1) - yes
    # Clue 12: short in 6 - yes
    
    # Prepare solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "PhoneModel"],
            "rows": []
        }
    }
    
    for house in range(1, 7):
        row = [
            str(house),
            name_assignments.get(house, ''),
            height_assignments.get(house, ''),
            phone_assignments.get(house, '')
        ]
        solution["solution"]["rows"].append(row)
    
    return json.dumps(solution)

print(solve_puzzle())