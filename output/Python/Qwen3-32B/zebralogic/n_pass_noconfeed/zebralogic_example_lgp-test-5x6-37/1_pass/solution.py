import json

# Initialize houses
houses = [
    {'House': 1, 'Name': None, 'Hobby': None, 'FavoriteSport': None, 'HouseStyle': None, 'Children': None, 'Height': None},
    {'House': 2, 'Name': None, 'Hobby': None, 'FavoriteSport': None, 'HouseStyle': None, 'Children': None, 'Height': None},
    {'House': 3, 'Name': None, 'Hobby': None, 'FavoriteSport': None, 'HouseStyle': None, 'Children': None, 'Height': None},
    {'House': 4, 'Name': None, 'Hobby': None, 'FavoriteSport': None, 'HouseStyle': None, 'Children': None, 'Height': None},
    {'House': 5, 'Name': None, 'Hobby': None, 'FavoriteSport': None, 'HouseStyle': None, 'Children': None, 'Height': None},
]

# Apply direct clues
# Clue 20: house 5's style is victorian
houses[4]['HouseStyle'] = 'victorian'

# Clue 3: Peter is directly left of victorian (house 5) → house 4
houses[3]['Name'] = 'Peter'

# Clue 16: Peter is very tall
houses[3]['Height'] = 'very tall'

# Clue 5: very tall → baseball
houses[3]['FavoriteSport'] = 'baseball'

# Clue 2: house 2's height is tall
houses[1]['Height'] = 'tall'

# Clue 4: Alice is tall → house 2
houses[1]['Name'] = 'Alice'

# Clue 8: house 2's hobby is gardening
houses[1]['Hobby'] = 'gardening'

# Clue 14: house 5's child is Fred
houses[4]['Children'] = 'Fred'

# Determine modern house (based on deductions)
# Modern house has cooking, Samantha, tennis
# From our deduction, it's house 3 (index 2)
houses[2]['Hobby'] = 'cooking'
houses[2]['HouseStyle'] = 'modern'
houses[2]['Children'] = 'Samantha'
houses[2]['FavoriteSport'] = 'tennis'

# Clue 17: ranch is left of cooking (house 3) → house 2 is ranch
houses[1]['HouseStyle'] = 'ranch'

# Clue 13: craftsman has average height → house 0
houses[0]['HouseStyle'] = 'craftsman'
houses[0]['Height'] = 'average'

# Clue 1: average → Meredith
houses[0]['Children'] = 'Meredith'

# Clue 6: Meredith's house is next to Timothy → house 1 has Timothy
houses[1]['Children'] = 'Timothy'

# Remaining children for house 3 (index 2) is Samantha, house 4 (index 3) is Bella, house 5 is Fred
houses[3]['Children'] = 'Bella'

# Heights for house 2 and 5: very short and short
# From deduction, house 3 (index 2) has very short, house 5 has short
houses[2]['Height'] = 'very short'
houses[4]['Height'] = 'short'

# Clue 15: short → basketball
houses[4]['FavoriteSport'] = 'basketball'

# Remaining sports for house 0 and 1: swimming and soccer
# Clue 11: soccer not in house 1 → house 0: swimming, house 1: soccer
houses[0]['FavoriteSport'] = 'swimming'
houses[1]['FavoriteSport'] = 'soccer'

# Hobbies for remaining houses: painting and photography
# Bob's hobby is painting → house 5 (index 4)
houses[4]['Hobby'] = 'painting'
houses[4]['Name'] = 'Bob'

# Remaining hobby for house 3 (index 3) is photography
houses[3]['Hobby'] = 'photography'

# Names for remaining houses: house 0 is Eric, house 2 is Arnold
houses[0]['Name'] = 'Eric'
houses[2]['Name'] = 'Arnold'

# HouseStyle for house 3 (index 3) is colonial
houses[3]['HouseStyle'] = 'colonial'

# Now, construct the solution
solution = {
    "solution": {
        "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
        "rows": []
    }
}

for house in houses:
    row = [
        str(house['House']),
        house['Name'],
        house['Hobby'],
        house['FavoriteSport'],
        house['HouseStyle'],
        house['Children'],
        house['Height']
    ]
    solution["solution"]["rows"].append(row)

# Print as JSON
print(json.dumps(solution, indent=2))