import itertools
import json

names = ['Eric', 'Alice', 'Peter', 'Arnold']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']

for name_perm in itertools.permutations(names):
    # Check if Arnold is in house 3 or 4 (0-based index 2 or 3)
    if name_perm[2] != 'Arnold' and name_perm[3] != 'Arnold':
        continue

    # Determine Arnold's house (1-based)
    arnold_house = None
    arnold_index = None
    for i in range(4):
        if name_perm[i] == 'Arnold':
            arnold_house = i + 1
            arnold_index = i  # 0-based index
            break

    # Assign sports
    sports_list = [None] * 4
    sports_list[0] = 'tennis'  # house 1
    sports_list[1] = 'soccer'  # house 2
    # Arnold's sport is basketball
    sports_list[arnold_index] = 'basketball'
    # remaining sport is swimming
    for i in range(4):
        if sports_list[i] is None:
            sports_list[i] = 'swimming'
            break

    # Generate car permutations for non-Eric positions
    non_eric_positions = []
    for i in range(4):
        if name_perm[i] != 'Eric':
            non_eric_positions.append(i)

    # The cars for non-Eric are permutations of ['toyota camry', 'honda civic', 'ford f150']
    for car_perm in itertools.permutations(['toyota camry', 'honda civic', 'ford f150']):
        car_list = [''] * 4
        for idx, pos in enumerate(non_eric_positions):
            car_list[pos] = car_perm[idx]
        # Eric's car is tesla
        for i in range(4):
            if name_perm[i] == 'Eric':
                car_list[i] = 'tesla model 3'
                break

        # Find Toyota Camry position
        toyota_pos = None
        for i in range(4):
            if car_list[i] == 'toyota camry':
                toyota_pos = i
                break

        # Check adjacency to Arnold
        if abs(toyota_pos - arnold_index) != 1:
            continue

        # Check Honda Civic is to the right of Toyota Camry
        honda_pos = None
        for i in range(4):
            if car_list[i] == 'honda civic':
                honda_pos = i
                break
        if honda_pos <= toyota_pos:
            continue

        # Now assign smoothies
        # Find Peter's position
        peter_pos = None
        for i in range(4):
            if name_perm[i] == 'Peter':
                peter_pos = i
                break

        # Generate smoothie permutations
        for smoothie_perm in itertools.permutations(smoothies):
            # Check Peter's smoothie
            if smoothie_perm[peter_pos] != 'dragonfruit':
                continue
            # Check Toyota Camry's smoothie is desert
            if smoothie_perm[toyota_pos] != 'desert':
                continue
            # Check watermelon not in house 1 (index 0)
            if smoothie_perm[0] == 'watermelon':
                continue

            # Assign flowers
            flower_list = [''] * 4
            for i in range(4):
                if name_perm[i] == 'Eric':
                    flower_list[i] = 'roses'
                elif name_perm[i] == 'Arnold':
                    flower_list[i] = 'lilies'
                elif car_list[i] == 'honda civic':
                    flower_list[i] = 'daffodils'
                else:
                    flower_list[i] = 'carnations'

            # Check all flowers are unique
            if len(set(flower_list)) != 4:
                continue

            # Build the solution
            rows = []
            for house_num in range(1, 5):
                idx = house_num - 1
                row = [
                    str(house_num),
                    name_perm[idx],
                    smoothie_perm[idx],
                    sports_list[idx],
                    car_list[idx],
                    flower_list[idx]
                ]
                rows.append(row)

            solution = {
                "solution": {
                    "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                    "rows": rows
                }
            }

            print(json.dumps(solution, indent=2))
            exit()

# If no solution found (though there should be one)
print(json.dumps({"solution": {"header": [], "rows": []}}))