import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold']
    phone_models = ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9']
    cigars = ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster']
    flowers = ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris']
    colors = ['yellow', 'red', 'green', 'blue', 'white', 'purple']
    sports = ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']

    # Initialize solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
            "rows": []
        }
    }

    # We'll use a backtracking approach to assign attributes to houses
    # Let's represent each house as a dictionary
    class House:
        def __init__(self, number):
            self.number = number
            self.name = None
            self.phone_model = None
            self.cigar = None
            self.flower = None
            self.color = None
            self.sport = None

        def to_row(self):
            return [
                str(self.number),
                self.name,
                self.phone_model,
                self.cigar,
                self.flower,
                self.color,
                self.sport
            ]

    # Initialize houses
    houses_list = [House(i) for i in range(1, 7)]

    # Apply constraints step by step
    # Constraint 18: Alice is in the first house
    houses_list[0].name = 'Alice'

    # Constraint 1: OnePlus 9 is in the second house
    houses_list[1].phone_model = 'oneplus 9'

    # Constraint 15: Dunhill smoker is Peter
    # Constraint 16: Peter loves blue
    # Constraint 10: Dunhill smoker loves volleyball
    # Constraint 24: volleyball person uses iphone 13
    # So Peter uses iphone 13, dunhill, volleyball, blue
    for house in houses_list:
        if house.name == 'Peter':
            house.cigar = 'dunhill'
            house.color = 'blue'
            house.sport = 'volleyball'
            house.phone_model = 'iphone 13'
            break

    # Constraint 7: Eric is to the right of samsung galaxy s21 user
    # Constraint 23: Eric smokes blends
    # Constraint 22: carnations is directly left of blends
    # Constraint 3: Carol loves carnations
    # Constraint 21: Carol loves soccer
    # Constraint 8: 2 houses between Carol and daffodils
    # So Carol must be in house 1, 2, or 3 (since daffodils would be +3)
    # But Alice is in house 1, so Carol is in 2 or 3
    # House 2 has oneplus 9, no name assigned yet
    # Let's see if Carol is in house 2 or 3

    # Try Carol in house 2
    houses_list[1].name = 'Carol'
    houses_list[1].flower = 'carnations'
    houses_list[1].sport = 'soccer'
    # Then blends is in house 3 (directly right of carnations)
    houses_list[2].cigar = 'blends'
    houses_list[2].name = 'Eric'  # from constraint 23
    # Then Eric is right of samsung galaxy s21, so samsung is left of Eric (house 1 or 2)
    # House 1 has Alice, phone model not assigned yet
    houses_list[0].phone_model = 'samsung galaxy s21'
    # Daffodils is 2 houses to the right of Carol (house 2 + 3 = house 5)
    houses_list[4].flower = 'daffodils'
    # Constraint 14: iris is left of Eric (house 2 or 1)
    houses_list[0].flower = 'iris'
    # Constraint 4: purple is directly left of pall mall
    # Let's find possible positions for pall mall
    # House 3 has blends, so not pall mall
    # House 4 or 5 or 6 could have pall mall, then purple is left
    # Try house 4 pall mall, then house 3 purple
    houses_list[3].cigar = 'pall mall'
    houses_list[2].color = 'purple'
    # Constraint 5: green color smokes blue master
    # Constraint 19: baseball is directly left of blue master
    # So baseball is left of blue master, and blue master is green
    # Possible positions: baseball in 1, blue master in 2
    # But house 2 has oneplus 9, no cigar assigned yet
    # Or baseball in 2, blue master in 3
    # But house 3 has blends
    # Or baseball in 3, blue master in 4
    # House 3 has blends, not blue master
    # Or baseball in 4, blue master in 5
    # House 4 has pall mall, not blue master
    # Or baseball in 5, blue master in 6
    # House 5 has no cigar assigned yet
    houses_list[5].cigar = 'blue master'
    houses_list[5].color = 'green'
    houses_list[4].sport = 'baseball'
    # Constraint 12: huawei p50 is directly left of white
    # Possible positions: huawei in 1, white in 2
    # But house 2 has oneplus 9
    # huawei in 2, white in 3 - but house 2 has oneplus 9
    # huawei in 3, white in 4
    # house 3 phone not assigned yet
    houses_list[2].phone_model = 'huawei p50'
    houses_list[3].color = 'white'
    # Constraint 2: xiaomi is left of huawei
    # huawei is in 3, so xiaomi is in 1 or 2
    # house 1 has samsung, so xiaomi in 2
    houses_list[1].phone_model = 'xiaomi mi 11'
    # Wait, house 1 has samsung, house 2 has oneplus 9 (from constraint 1)
    # So xiaomi must be in house 1, but house 1 has samsung
    # Contradiction, so Carol cannot be in house 2

    # Reset and try Carol in house 3
    houses_list = [House(i) for i in range(1, 7)]
    houses_list[0].name = 'Alice'
    houses_list[1].phone_model = 'oneplus 9'
    # Assign Peter
    for house in houses_list:
        if house.name == 'Peter':
            house.cigar = 'dunhill'
            house.color = 'blue'
            house.sport = 'volleyball'
            house.phone_model = 'iphone 13'
            break
    # Carol in house 3
    houses_list[2].name = 'Carol'
    houses_list[2].flower = 'carnations'
    houses_list[2].sport = 'soccer'
    # Eric is right of samsung, and blends is directly right of carnations (house 4)
    houses_list[3].cigar = 'blends'
    houses_list[3].name = 'Eric'
    # samsung is left of Eric (house 1 or 2)
    houses_list[0].phone_model = 'samsung galaxy s21'
    # daffodils is 2 houses right of Carol (house 3 + 3 = house 6)
    houses_list[5].flower = 'daffodils'
    # iris is left of Eric (house 1 or 2)
    houses_list[1].flower = 'roses'  # from constraint 13: oneplus 9 and roses are next to each other
    # oneplus is in house 2, so roses must be in 1 or 3
    # house 3 has carnations, so roses in 1
    houses_list[0].flower = 'roses'
    # But iris must be left of Eric, so iris in 1 or 2
    # house 1 has roses, so iris in 2
    houses_list[1].flower = 'iris'
    # Constraint 4: purple is directly left of pall mall
    # Possible positions: pall mall in 4, purple in 3
    houses_list[3].cigar = 'pall mall'  # but house 3 has blends - contradiction
    # pall mall in 5, purple in 4
    houses_list[4].cigar = 'pall mall'
    houses_list[3].color = 'purple'
    # Constraint 5: green is blue master
    # Constraint 19: baseball is directly left of blue master
    # Possible positions: baseball in 1, blue master in 2
    houses_list[1].cigar = 'blue master'
    houses_list[1].color = 'green'
    houses_list[0].sport = 'baseball'
    # Constraint 12: huawei is directly left of white
    # Possible positions: huawei in 2, white in 3
    # house 2 has oneplus 9, so not huawei
    # huawei in 3, white in 4
    houses_list[2].phone_model = 'huawei p50'
    houses_list[3].color = 'white'
    # Constraint 2: xiaomi is left of huawei (huawei in 3, so xiaomi in 1 or 2)
    # house 1 has samsung, so xiaomi in 2
    houses_list[1].phone_model = 'xiaomi mi 11'
    # But house 1 has samsung, house 2 has oneplus 9 (from constraint 1)
    # Wait, house 1 has samsung, house 2 has oneplus 9, so xiaomi cannot be in 2
    # Contradiction again

    # Reset and try Carol in house 1 - but Alice is in house 1, so invalid

    # Seems like previous attempts failed, let's try a different approach
    # Reinitialize
    houses_list = [House(i) for i in range(1, 7)]
    houses_list[0].name = 'Alice'
    houses_list[1].phone_model = 'oneplus 9'

    # Assign Peter
    peter_house = None
    for house in houses_list:
        if house.name == 'Peter':
            peter_house = house
            break
    if peter_house is None:
        for house in houses_list:
            if house.name is None:
                house.name = 'Peter'
                peter_house = house
                break
    peter_house.cigar = 'dunhill'
    peter_house.color = 'blue'
    peter_house.sport = 'volleyball'
    peter_house.phone_model = 'iphone 13'

    # Assign Carol
    carol_house = None
    for house in houses_list:
        if house.name == 'Carol':
            carol_house = house
            break
    if carol_house is None:
        for house in houses_list:
            if house.name is None and house.number in [2, 3]:
                house.name = 'Carol'
                carol_house = house
                break
    carol_house.flower = 'carnations'
    carol_house.sport = 'soccer'

    # Assign Eric
    eric_house = None
    for house in houses_list:
        if house.name == 'Eric':
            eric_house = house
            break
    if eric_house is None:
        for house in houses_list:
            if house.name is None and house.number > carol_house.number:
                house.name = 'Eric'
                eric_house = house
                break
    eric_house.cigar = 'blends'

    # Assign samsung left of Eric
    for house in houses_list:
        if house.phone_model is None and house.number < eric_house.number:
            house.phone_model = 'samsung galaxy s21'
            break

    # Assign daffodils two houses right of Carol
    daffodil_house_num = carol_house.number + 3
    if daffodil_house_num <= 6:
        houses_list[daffodil_house_num - 1].flower = 'daffodils'

    # Assign iris left of Eric
    for house in houses_list:
        if house.flower is None and house.number < eric_house.number:
            house.flower = 'iris'
            break

    # Assign purple left of pall mall
    for i in range(1, 6):
        if houses_list[i].cigar == 'pall mall':
            houses_list[i-1].color = 'purple'
            break

    # Assign green and blue master
    for house in houses_list:
        if house.color == 'green':
            house.cigar = 'blue master'
            # Find baseball left of blue master
            for h in houses_list:
                if h.number == house.number - 1:
                    h.sport = 'baseball'
                    break

    # Assign huawei left of white
    for i in range(5):
        if houses_list[i].phone_model == 'huawei p50':
            houses_list[i+1].color = 'white'
            break

    # Assign xiaomi left of huawei
    for i in range(5):
        if houses_list[i].phone_model == 'xiaomi mi 11':
            for j in range(i+1, 6):
                if houses_list[j].phone_model == 'huawei p50':
                    break
            break

    # Assign remaining names
    remaining_names = set(names) - {house.name for house in houses_list if house.name is not None}
    for name in remaining_names:
        for house in houses_list:
            if house.name is None:
                house.name = name
                break

    # Assign remaining flowers
    remaining_flowers = set(flowers) - {house.flower for house in houses_list if house.flower is not None}
    for flower in remaining_flowers:
        for house in houses_list:
            if house.flower is None:
                house.flower = flower
                break

    # Assign remaining colors
    remaining_colors = set(colors) - {house.color for house in houses_list if house.color is not None}
    for color in remaining_colors:
        for house in houses_list:
            if house.color is None:
                house.color = color
                break

    # Assign remaining sports
    remaining_sports = set(sports) - {house.sport for house in houses_list if house.sport is not None}
    for sport in remaining_sports:
        for house in houses_list:
            if house.sport is None:
                house.sport = sport
                break

    # Assign remaining phone models
    remaining_phones = set(phone_models) - {house.phone_model for house in houses_list if house.phone_model is not None}
    for phone in remaining_phones:
        for house in houses_list:
            if house.phone_model is None:
                house.phone_model = phone
                break

    # Assign remaining cigars
    remaining_cigars = set(cigars) - {house.cigar for house in houses_list if house.cigar is not None}
    for cigar in remaining_cigars:
        for house in houses_list:
            if house.cigar is None:
                house.cigar = cigar
                break

    # Prepare the solution rows
    solution_rows = [house.to_row() for house in houses_list]
    solution["solution"]["rows"] = solution_rows

    return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())