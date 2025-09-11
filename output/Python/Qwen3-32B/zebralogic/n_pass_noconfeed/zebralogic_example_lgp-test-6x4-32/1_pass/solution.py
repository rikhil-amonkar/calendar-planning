import json

# Initialize the houses with known values
houses = [
    {'House': 1, 'Name': None, 'HouseStyle': None, 'MusicGenre': 'country', 'Hobby': None},
    {'House': 2, 'Name': None, 'HouseStyle': None, 'MusicGenre': None, 'Hobby': None},
    {'House': 3, 'Name': 'Bob', 'HouseStyle': None, 'MusicGenre': None, 'Hobby': None},
    {'House': 4, 'Name': None, 'HouseStyle': None, 'MusicGenre': None, 'Hobby': None},
    {'House': 5, 'Name': None, 'HouseStyle': None, 'MusicGenre': 'rock', 'Hobby': None},
    {'House': 6, 'Name': None, 'HouseStyle': None, 'MusicGenre': None, 'Hobby': None},
]

# Apply clue 4 and 8: Arnold in house 1, craftsman style, Victorian in house 4
houses[0]['Name'] = 'Arnold'
houses[0]['HouseStyle'] = 'craftsman'
houses[3]['HouseStyle'] = 'victorian'

# Apply clue 10: Victorian hobby is woodworking
houses[3]['Hobby'] = 'woodworking'

# Apply clue 2 and 3: classical in house 3
houses[2]['MusicGenre'] = 'classical'

# Apply clue 7 and 3: Carol in house 2 with hip hop and mediterranean style
houses[1]['Name'] = 'Carol'
houses[1]['MusicGenre'] = 'hip hop'
houses[1]['HouseStyle'] = 'mediterranean'

# Apply clue 5 and 9: Eric in house 5 with ranch style and jazz in house 4
houses[4]['Name'] = 'Eric'
houses[4]['HouseStyle'] = 'ranch'
houses[4]['Hobby'] = 'gardening'  # clue 14
houses[3]['MusicGenre'] = 'jazz'

# Remaining music genre for house 6 is pop
houses[5]['MusicGenre'] = 'pop'

# Apply clue 12: colonial in house 3, painter in house 1
houses[2]['HouseStyle'] = 'colonial'
houses[0]['Hobby'] = 'painting'

# Remaining styles for house 6 is modern
houses[5]['HouseStyle'] = 'modern'

# Apply clue 6: knitting in house 3
houses[2]['Hobby'] = 'knitting'

# Remaining hobbies for house 2 is cooking
houses[1]['Hobby'] = 'cooking'

# Assign remaining names and hobbies
# Alice's hobby is photography (clue 13)
houses[5]['Name'] = 'Alice'
houses[5]['Hobby'] = 'photography'

# Remaining name for house 4 is Peter
houses[3]['Name'] = 'Peter'

# Convert to the required JSON structure
solution = {
    "solution": {
        "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
        "rows": [
            [
                str(house['House']),
                house['Name'],
                house['HouseStyle'],
                house['MusicGenre'],
                house['Hobby']
            ] for house in houses
        ]
    }
}

print(json.dumps(solution, indent=2))