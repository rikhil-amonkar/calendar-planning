import json

# Initialize the houses with empty dictionaries
houses = [{} for _ in range(6)]  # Index 0 is House 1, Index 5 is House 6

# Apply direct clues from the problem
# Clue 8: Samsung Galaxy S21 is in the fifth house (index 4)
houses[4]['PhoneModel'] = 'samsung galaxy s21'

# Clue 10: The person who uses Samsung Galaxy S21 is Bob (index 4)
houses[4]['Name'] = 'Bob'

# Clue 15: Samsung Galaxy S21 is directly left of iPhone 13 → House 6 (index 5) uses iPhone 13
houses[5]['PhoneModel'] = 'iphone 13'

# Clue 12: Samsung Galaxy S21 is left of Peter → Peter is in House 6 (index 5)
houses[5]['Name'] = 'Peter'

# Clue 14: Peter is the British person
houses[5]['Nationality'] = 'brit'

# Clue 13: Peter loves blue
houses[5]['Color'] = 'blue'

# Clue 2: One house between the Dane and the British person → Dane is in House 4 (index 3)
houses[3]['Nationality'] = 'dane'

# Clue 11: The Dane loves yellow
houses[3]['Color'] = 'yellow'

# Clue 4: Arnold is directly left of Alice → Arnold in House 2 (index 1), Alice in House 3 (index 2)
houses[1]['Name'] = 'Arnold'
houses[2]['Name'] = 'Alice'

# Clue 5: Alice is the German
houses[2]['Nationality'] = 'german'

# Clue 1: Carol is not in the third house (index 2 is Alice), so Carol must be in House 1 (index 0)
houses[0]['Name'] = 'Carol'

# House 4 (index 3) must be Eric (remaining name)
houses[3]['Name'] = 'Eric'

# Clue 3: Carol's favorite color is green
houses[0]['Color'] = 'green'

# Clue 16: The Norwegian loves purple → Arnold (House 2, index 1) is the Norwegian
houses[1]['Nationality'] = 'norwegian'

# Clue 17: The Chinese uses Xiaomi Mi 11 → Carol (House 1, index 0) is Chinese
houses[0]['Nationality'] = 'chinese'
houses[0]['PhoneModel'] = 'xiaomi mi 11'

# Clue 6: The OnePlus 9 user loves purple → Norwegian (House 2, index 1) uses OnePlus 9
houses[1]['PhoneModel'] = 'oneplus 9'

# Remaining phones for Houses 3 and 4 are Google Pixel 6 and Huawei P50
# Clue 7: Huawei P50 is not in the third house (index 2) → Assign Google Pixel 6 to House 3 (index 2), Huawei P50 to House 4 (index 3)
houses[2]['PhoneModel'] = 'google pixel 6'
houses[3]['PhoneModel'] = 'huawei p50'

# Clue 16: Norwegian (House 2, index 1) loves purple → Already set
# Clue 9: White is to the right of red → Assign red to House 3 (index 2), white to House 5 (index 4)
houses[2]['Color'] = 'red'
houses[4]['Color'] = 'white'

# Build the solution dictionary
solution = {
    "solution": {
        "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
        "rows": []
    }
}

# Populate the rows with the solved data
for i in range(6):
    house_num = i + 1
    name = houses[i]['Name']
    phone_model = houses[i]['PhoneModel']
    nationality = houses[i]['Nationality']
    color = houses[i]['Color']
    solution['solution']['rows'].append([
        str(house_num), name, phone_model, nationality, color
    ])

# Output the solution in JSON format
print(json.dumps(solution))