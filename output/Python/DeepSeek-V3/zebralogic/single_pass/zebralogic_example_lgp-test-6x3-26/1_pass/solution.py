import json
from itertools import permutations

def solve_puzzle():
    # Define all possible attributes
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    # Create houses
    houses = [{'number': str(i+1)} for i in range(6)]
    
    # Apply clues one by one
    
    # Clue 9: The person who is super tall is in the first house.
    for house in houses:
        if house['number'] == '1':
            house['height'] = 'super tall'
    
    # Clue 12: The person who is short is in the sixth house.
    for house in houses:
        if house['number'] == '6':
            house['height'] = 'short'
    
    # Clue 8: The person who is tall is Arnold.
    # So Arnold's height is tall
    
    # Clue 4: Carol is the person who is very tall.
    # So Carol's height is very tall
    
    # Clue 10: The person who uses a Xiaomi Mi 11 is Carol.
    # So Carol's phone is xiaomi mi 11
    
    # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short.
    # Since short is in house 6, oneplus 9 is in house 5
    for house in houses:
        if house['number'] == '5':
            house['phone'] = 'oneplus 9'
    
    # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short.
    # Short is in 6, so google pixel 6 is in 4 (since one house between means 4 and 6)
    for house in houses:
        if house['number'] == '4':
            house['phone'] = 'google pixel 6'
    
    # Clue 3: The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
    # google pixel 6 is in 4, so very short is in 5 or 6. But 6 is short, so very short is in 5
    for house in houses:
        if house['number'] == '5':
            house['height'] = 'very short'
    
    # Clue 11: The person who uses a Google Pixel 6 is somewhere to the right of Eric.
    # google pixel 6 is in 4, so Eric is in 1, 2, or 3
    
    # Clue 1: Bob is directly left of the person who is tall.
    # So Bob is in position n, tall person is in n+1
    # tall person is Arnold (from clue 8)
    # So Arnold is in n+1, Bob is in n
    
    # Possible positions for Arnold (tall): 2-6 (since someone is left)
    # But house 1 has super tall, 5 has very short, 6 has short
    # So Arnold could be in 2,3, or 4 (but 4 has google pixel 6, no height assigned yet)
    # Let's consider possibilities:
    # If Arnold is in 2:
    #   Bob is in 1
    # But house 1 has super tall, no name assigned yet
    # If Arnold is in 3:
    #   Bob is in 2
    # If Arnold is in 4:
    #   Bob is in 3
    
    # Let's explore Arnold in 2:
    # Bob in 1
    # But house 1's name would be Bob, but height is super tall
    # From clue 9, super tall is in 1, but no name assigned yet
    # So possible
    
    # Let's try Arnold in 2:
    for house in houses:
        if house['number'] == '2':
            house['name'] = 'Arnold'
            house['height'] = 'tall'
        if house['number'] == '1':
            house['name'] = 'Bob'
    
    # From clue 11: Eric is left of google pixel 6 (house 4), so Eric is in 1,2, or 3
    # But 1 is Bob, 2 is Arnold, so Eric must be in 3
    for house in houses:
        if house['number'] == '3':
            house['name'] = 'Eric'
    
    # From clue 2: Peter is somewhere to the left of the person who uses an iPhone 13.
    # We haven't placed Peter yet. Remaining names: Alice, Peter, Carol
    # Positions left: 4,5,6 (names not assigned yet)
    # But house 4: name not assigned, phone is google pixel 6
    # house 5: name not assigned, phone is oneplus 9, height very short
    # house 6: name not assigned, height short
    
    # From clue 4: Carol is very tall
    # From heights left: average, very tall (since super tall in 1, tall in 2, very short in 5, short in 6)
    # Carol must be in a house with height very tall
    # Heights assigned so far:
    # 1: super tall, 2: tall, 5: very short, 6: short
    # So very tall must be in 3 or 4
    # 3: name is Eric, height not assigned
    # 4: name not assigned, height not assigned
    
    # From clue 4: Carol is very tall
    # So Carol is in 3 or 4 with height very tall
    # But 3's name is Eric, so Carol must be in 4
    for house in houses:
        if house['number'] == '4':
            house['name'] = 'Carol'
            house['height'] = 'very tall'
    
    # Then house 3's height must be average (only remaining)
    for house in houses:
        if house['number'] == '3':
            house['height'] = 'average'
    
    # Now assign remaining names: Alice and Peter
    # Positions left: 5 and 6
    # From names left: Alice, Peter
    
    # From clue 2: Peter is left of iphone 13
    # So iphone 13 must be to the right of Peter
    # Possible positions:
    # If Peter is in 5, iphone 13 is in 6
    # If Peter is in 4, but 4 is Carol
    # So Peter must be in 5, iphone 13 in 6
    for house in houses:
        if house['number'] == '5':
            house['name'] = 'Peter'
        if house['number'] == '6':
            house['name'] = 'Alice'
    
    # Now assign phones
    # Phones assigned so far:
    # 4: google pixel 6, 5: oneplus 9
    # From clue 10: Carol uses xiaomi mi 11
    # Carol is in 4, but 4's phone is google pixel 6 - contradiction!
    # Wait, this means our assumption that Arnold is in 2 is wrong
    
    # Let's backtrack and try Arnold in 3
    # Reset houses
    houses = [{'number': str(i+1)} for i in range(6)]
    
    # Reapply fixed clues
    # House 1: super tall (clue 9)
    for house in houses:
        if house['number'] == '1':
            house['height'] = 'super tall'
    
    # House 6: short (clue 12)
    for house in houses:
        if house['number'] == '6':
            house['height'] = 'short'
    
    # House 5: oneplus 9 (clue 7)
    for house in houses:
        if house['number'] == '5':
            house['phone'] = 'oneplus 9'
    
    # House 4: google pixel 6 (clue 5)
    for house in houses:
        if house['number'] == '4':
            house['phone'] = 'google pixel 6'
    
    # House 5: very short (clue 3)
    for house in houses:
        if house['number'] == '5':
            house['height'] = 'very short'
    
    # Now Arnold is in 3, Bob in 2 (clue 1 and 8)
    for house in houses:
        if house['number'] == '3':
            house['name'] = 'Arnold'
            house['height'] = 'tall'
        if house['number'] == '2':
            house['name'] = 'Bob'
    
    # From clue 11: Eric is left of google pixel 6 (house 4), so Eric is in 1,2, or 3
    # 2 is Bob, 3 is Arnold, so Eric is in 1
    for house in houses:
        if house['number'] == '1':
            house['name'] = 'Eric'
    
    # From clue 4: Carol is very tall
    # Heights left: average, very tall
    # Possible positions: 4,6 (since 1: super tall, 2: ?, 3: tall, 5: very short)
    # 6 is short, so Carol must be in 4 with very tall
    for house in houses:
        if house['number'] == '4':
            house['name'] = 'Carol'
            house['height'] = 'very tall'
    
    # From clue 10: Carol uses xiaomi mi 11
    for house in houses:
        if house['number'] == '4':
            house['phone'] = 'xiaomi mi 11'
    # But house 4's phone was google pixel 6 from earlier - contradiction!
    # So this arrangement is invalid
    
    # Let's try Arnold in 4
    # Reset houses
    houses = [{'number': str(i+1)} for i in range(6)]
    
    # Reapply fixed clues
    # House 1: super tall (clue 9)
    for house in houses:
        if house['number'] == '1':
            house['height'] = 'super tall'
    
    # House 6: short (clue 12)
    for house in houses:
        if house['number'] == '6':
            house['height'] = 'short'
    
    # House 5: oneplus 9 (clue 7)
    for house in houses:
        if house['number'] == '5':
            house['phone'] = 'oneplus 9'
    
    # House 4: google pixel 6 (clue 5)
    for house in houses:
        if house['number'] == '4':
            house['phone'] = 'google pixel 6'
    
    # House 5: very short (clue 3)
    for house in houses:
        if house['number'] == '5':
            house['height'] = 'very short'
    
    # Arnold is in 4, Bob in 3 (clue 1 and 8)
    for house in houses:
        if house['number'] == '4':
            house['name'] = 'Arnold'
            house['height'] = 'tall'
        if house['number'] == '3':
            house['name'] = 'Bob'
    
    # From clue 11: Eric is left of google pixel 6 (house 4), so Eric is in 1,2, or 3
    # 3 is Bob, so Eric is in 1 or 2
    # House 1: name not assigned, height super tall
    # House 2: name not assigned
    
    # From clue 4: Carol is very tall
    # Heights left: average, very tall
    # Possible positions: 2,5,6
    # 5 is very short, 6 is short, so Carol must be in 2 with very tall
    for house in houses:
        if house['number'] == '2':
            house['name'] = 'Carol'
            house['height'] = 'very tall'
    
    # From clue 10: Carol uses xiaomi mi 11
    for house in houses:
        if house['number'] == '2':
            house['phone'] = 'xiaomi mi 11'
    
    # Now assign Eric to 1
    for house in houses:
        if house['number'] == '1':
            house['name'] = 'Eric'
    
    # Remaining names: Alice, Peter
    # Positions left: 5,6
    # From clue 2: Peter is left of iphone 13
    # So iphone 13 must be to the right of Peter
    # If Peter is in 5, iphone 13 is in 6
    for house in houses:
        if house['number'] == '5':
            house['name'] = 'Peter'
        if house['number'] == '6':
            house['name'] = 'Alice'
            house['phone'] = 'iphone 13'
    
    # Now assign remaining phones
    # Phones assigned so far:
    # 2: xiaomi mi 11, 4: google pixel 6, 5: oneplus 9, 6: iphone 13
    # Remaining phones: samsung galaxy s21, huawei p50
    # From clue 6: samsung galaxy s21 is not in first house
    # So house 1 cannot have samsung galaxy s21
    # House 1: phone not assigned, options: huawei p50, samsung galaxy s21
    # So house 1 must have huawei p50
    for house in houses:
        if house['number'] == '1':
            house['phone'] = 'huawei p50'
    
    # Then house 3 must have samsung galaxy s21
    for house in houses:
        if house['number'] == '3':
            house['phone'] = 'samsung galaxy s21'
    
    # Now assign remaining heights
    # Heights assigned:
    # 1: super tall, 2: very tall, 4: tall, 5: very short, 6: short
    # So house 3 must be average
    for house in houses:
        if house['number'] == '3':
            house['height'] = 'average'
    
    # Verify all clues are satisfied
    # All constraints should be satisfied now
    
    # Prepare the output
    solution = {
        "solution": {
            "header": ["House", "Name", "height", "phone"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [
            house['number'],
            house.get('name', ''),
            house.get('height', ''),
            house.get('phone', '')
        ]
        solution["solution"]["rows"].append(row)
    
    return json.dumps(solution, indent=2)

print(solve_puzzle())