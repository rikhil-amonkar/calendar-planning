import json

# Initialize 5 houses with empty attributes
houses = [{} for _ in range(5)]  # 0-based index for houses 1-5

# Apply clues step by step
# Clue 20: house 5 is Victorian
houses[4]['HouseStyle'] = 'victorian'

# Clue 3: Peter is directly left of Victorian (house 5) → house 4
houses[3]['Name'] = 'Peter'

# Clue 16: Peter is very tall
houses[3]['Height'] = 'very tall'

# Clue 5: Peter's favorite sport is baseball
houses[3]['FavoriteSport'] = 'baseball'

# Clue 2 and 4: house 2 (index 1) has height 'tall' and name Alice
houses[1]['Height'] = 'tall'
houses[1]['Name'] = 'Alice'

# Clue 8: house 2's Hobby is gardening
houses[1]['Hobby'] = 'gardening'

# Clue 19 and 12: modern house has Hobby cooking and Child Samantha
# Assume modern is house 3 (index 2)
houses[2]['HouseStyle'] = 'modern'
houses[2]['Hobby'] = 'cooking'
houses[2]['Children'] = 'Samantha'

# Clue 10: modern's FavoriteSport is tennis
houses[2]['FavoriteSport'] = 'tennis'

# Clue 17: ranch is to the left of cooking (modern). Assume house 1 is ranch
houses[1]['HouseStyle'] = 'ranch'

# Clue 13: craftsman has average height → assume house 0 is craftsman
houses[0]['HouseStyle'] = 'craftsman'
houses[0]['Height'] = 'average'

# Clue 1: average height has child Meredith
houses[0]['Children'] = 'Meredith'

# Clue 6: Meredith's house (0) and Timothy's mother are adjacent → house 1 has Timothy
houses[1]['Children'] = 'Timothy'

# Clue 14: house 5 has child Fred
houses[4]['Children'] = 'Fred'

# Remaining children for house 3 is Bella
houses[3]['Children'] = 'Bella'

# Clue 18: knitting next to gardening (house 1 has gardening) → house 0 has knitting
houses[0]['Hobby'] = 'knitting'

# Remaining hobbies: painting, photography for houses 3 and 4
# Clue 7: Bob's hobby is painting → assign to house 4
houses[4]['Hobby'] = 'painting'
houses[3]['Hobby'] = 'photography'

# Assign names: house 0 is Eric, house 2 is Arnold, house 4 is Bob
houses[0]['Name'] = 'Eric'
houses[2]['Name'] = 'Arnold'
houses[4]['Name'] = 'Bob'

# Assign heights for house 2 and 4: very short and short
# Assume house 2 is very short, house 4 is short
houses[2]['Height'] = 'very short'
houses[4]['Height'] = 'short'

# Clue 15: short has basketball → house 4's sport is basketball
houses[4]['FavoriteSport'] = 'basketball'

# Remaining sports: swimming and soccer for houses 0 and 1
# Clue 11: soccer not in house 0 → house 1 has soccer, house 0 has swimming
houses[0]['FavoriteSport'] = 'swimming'
houses[1]['FavoriteSport'] = 'soccer'

# Assign house styles for house 3 as colonial
houses[3]['HouseStyle'] = 'colonial'

# Now, construct the JSON
solution_data = {
    "solution": {
        "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
        "rows": []
    }
}

for i in range(5):
    house_num = i + 1
    row = [
        str(house_num),
        houses[i]['Name'],
        houses[i]['Hobby'],
        houses[i]['FavoriteSport'],
        houses[i]['HouseStyle'],
        houses[i]['Children'],
        houses[i]['Height']
    ]
    solution_data["solution"]["rows"].append(row)

print(json.dumps(solution_data, indent=2))