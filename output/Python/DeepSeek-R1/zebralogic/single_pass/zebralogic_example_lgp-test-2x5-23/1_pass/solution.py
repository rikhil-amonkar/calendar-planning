import json

def satisfies(candidate):
    for house in candidate:
        if house['Height'] == 'very short':
            if house['Food'] != 'pizza':
                return False
        if house['Education'] == 'high school':
            if house['Food'] != 'pizza':
                return False
        if house['Drink'] == 'tea':
            if house['Food'] != 'grilled cheese':
                return False
        if house['Name'] == 'Arnold':
            if house['Food'] != 'pizza':
                return False
    for house in candidate:
        if house['Food'] == 'grilled cheese':
            if house['House'] != 2:
                return False
    return True

domains = {
    'Name': ['Arnold', 'Eric'],
    'Education': ['associate', 'high school'],
    'Height': ['short', 'very short'],
    'Food': ['grilled cheese', 'pizza'],
    'Drink': ['tea', 'water']
}

solution_found = False
result = None

for name in domains['Name']:
    for edu in domains['Education']:
        for height in domains['Height']:
            for food in domains['Food']:
                for drink in domains['Drink']:
                    house1 = {
                        'House': 1,
                        'Name': name,
                        'Education': edu,
                        'Height': height,
                        'Food': food,
                        'Drink': drink
                    }
                    house2 = {
                        'House': 2,
                        'Name': next(x for x in domains['Name'] if x != name),
                        'Education': next(x for x in domains['Education'] if x != edu),
                        'Height': next(x for x in domains['Height'] if x != height),
                        'Food': next(x for x in domains['Food'] if x != food),
                        'Drink': next(x for x in domains['Drink'] if x != drink)
                    }
                    candidate = [house1, house2]
                    if satisfies(candidate):
                        solution_found = True
                        header = ["House", "Name", "Education", "Height", "Food", "Drink"]
                        row1 = [str(house1['House']), house1['Name'], house1['Education'], house1['Height'], house1['Food'], house1['Drink']]
                        row2 = [str(house2['House']), house2['Name'], house2['Education'], house2['Height'], house2['Food'], house2['Drink']]
                        result = {
                            "solution": {
                                "header": header,
                                "rows": [row1, row2]
                            }
                        }
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

if not solution_found:
    result = {"error": "No solution found"}

print(json.dumps(result))