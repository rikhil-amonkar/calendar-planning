import itertools
import json

names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']

valid_name_perms = []
for p in itertools.permutations(names):
    if p[3] == 'Alice':  # house 4 (index 3)
        valid_name_perms.append(p)

valid_height_perms = []
for p in itertools.permutations(heights):
    if p[4] == 'very short' and p[5] == 'tall':  # house 5 (index 4) and 6 (index 5)
        valid_height_perms.append(p)

valid_hair_perms = []
for p in itertools.permutations(hair_colors):
    if p[2] == 'gray':  # house 3 (index 2)
        valid_hair_perms.append(p)

for name_p in valid_name_perms:
    for hair_p in valid_hair_perms:
        for height_p in valid_height_perms:
            # Build houses
            houses = []
            for i in range(6):
                houses.append({
                    'Name': name_p[i],
                    'HairColor': hair_p[i],
                    'Height': height_p[i]
                })

            # Check clue 3: Arnold is short
            arnold_height = None
            for i, house in enumerate(houses):
                if house['Name'] == 'Arnold':
                    arnold_height = house['Height']
                    break
            if arnold_height != 'short':
                continue

            # Check clue 5: house 4's hair is not black
            if hair_p[3] == 'black':
                continue

            # Check clue 6: Eric's hair is red
            eric_hair = None
            for i, house in enumerate(houses):
                if house['Name'] == 'Eric':
                    eric_hair = house['HairColor']
                    break
            if eric_hair != 'red':
                continue

            # Check clue 7: super tall is to the right of average
            avg_pos = None
            super_tall_pos = None
            for i, h in enumerate(height_p):
                if h == 'average':
                    avg_pos = i
                elif h == 'super tall':
                    super_tall_pos = i
            if super_tall_pos is None or avg_pos is None or not (super_tall_pos > avg_pos):
                continue

            # Check clue 8: blonde is Carol
            blonde_index = hair_p.index('blonde')
            if name_p[blonde_index] != 'Carol':
                continue

            # Check clue 1: blonde is directly left of Bob
            if (blonde_index + 1 < 6) and name_p[blonde_index + 1] == 'Bob':
                pass
            else:
                continue

            # Check clue 11: Bob has brown hair
            bob_index = name_p.index('Bob')
            if hair_p[bob_index] != 'brown':
                continue

            # Check clue 9: gray (index 2) and red (Eric's index) are two apart
            eric_index = None
            for i, house in enumerate(houses):
                if house['Name'] == 'Eric':
                    eric_index = i
                    break
            if abs(2 - eric_index) != 2:
                continue

            # Check clue 13: blonde (Carol) is very tall
            if height_p[blonde_index] != 'very tall':
                continue

            # All constraints satisfied. Build the solution.
            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor", "Height"],
                    "rows": []
                }
            }
            for i in range(6):
                house_num = i + 1
                row = [
                    str(house_num),
                    houses[i]['Name'],
                    houses[i]['HairColor'],
                    houses[i]['Height']
                ]
                solution['solution']['rows'].append(row)

            print(json.dumps(solution))
            exit()