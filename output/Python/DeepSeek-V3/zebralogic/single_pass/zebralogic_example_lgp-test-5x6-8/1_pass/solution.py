import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice']
    house_styles = ['modern', 'craftsman', 'ranch', 'victorian', 'colonial']
    mothers = ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya']
    phone_models = ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21']
    drinks = ['coffee', 'water', 'root beer', 'tea', 'milk']
    animals = ['fish', 'dog', 'horse', 'bird', 'cat']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            for mother_perm in permutations(mothers):
                for phone_perm in permutations(phone_models):
                    for drink_perm in permutations(drinks):
                        for animal_perm in permutations(animals):
                            # Create a dictionary to hold the current assignment
                            solution = {
                                '1': {'Name': None, 'HouseStyle': None, 'Mother': None, 'PhoneModel': None, 'Drink': None, 'Animal': None},
                                '2': {'Name': None, 'HouseStyle': None, 'Mother': None, 'PhoneModel': None, 'Drink': None, 'Animal': None},
                                '3': {'Name': None, 'HouseStyle': None, 'Mother': None, 'PhoneModel': None, 'Drink': None, 'Animal': None},
                                '4': {'Name': None, 'HouseStyle': None, 'Mother': None, 'PhoneModel': None, 'Drink': None, 'Animal': None},
                                '5': {'Name': None, 'HouseStyle': None, 'Mother': None, 'PhoneModel': None, 'Drink': None, 'Animal': None}
                            }

                            # Assign current permutation to houses
                            for i, house in enumerate(houses):
                                solution[house]['Name'] = name_perm[i]
                                solution[house]['HouseStyle'] = style_perm[i]
                                solution[house]['Mother'] = mother_perm[i]
                                solution[house]['PhoneModel'] = phone_perm[i]
                                solution[house]['Drink'] = drink_perm[i]
                                solution[house]['Animal'] = animal_perm[i]

                            # Check all constraints
                            valid = True

                            # Clue 1: Google Pixel 6 is not in the first house
                            if solution['1']['PhoneModel'] == 'google pixel 6':
                                valid = False

                            # Clue 2: Alice only drinks water
                            for house in houses:
                                if solution[house]['Name'] == 'Alice' and solution[house]['Drink'] != 'water':
                                    valid = False
                                elif solution[house]['Name'] != 'Alice' and solution[house]['Drink'] == 'water':
                                    valid = False

                            # Clue 3: Colonial is right of huawei p50
                            huawei_house = None
                            colonial_house = None
                            for house in houses:
                                if solution[house]['PhoneModel'] == 'huawei p50':
                                    huawei_house = int(house)
                                if solution[house]['HouseStyle'] == 'colonial':
                                    colonial_house = int(house)
                            if huawei_house is not None and colonial_house is not None:
                                if colonial_house <= huawei_house:
                                    valid = False
                            else:
                                valid = False

                            # Clue 4: Horse keeper uses oneplus 9
                            for house in houses:
                                if solution[house]['Animal'] == 'horse' and solution[house]['PhoneModel'] != 'oneplus 9':
                                    valid = False
                                elif solution[house]['PhoneModel'] == 'oneplus 9' and solution[house]['Animal'] != 'horse':
                                    valid = False

                            # Clue 5: Ranch-style home has mother Kailyn
                            for house in houses:
                                if solution[house]['HouseStyle'] == 'ranch' and solution[house]['Mother'] != 'Kailyn':
                                    valid = False
                                elif solution[house]['Mother'] == 'Kailyn' and solution[house]['HouseStyle'] != 'ranch':
                                    valid = False

                            # Clue 6: Root beer lover is cat lover
                            for house in houses:
                                if solution[house]['Drink'] == 'root beer' and solution[house]['Animal'] != 'cat':
                                    valid = False
                                elif solution[house]['Animal'] == 'cat' and solution[house]['Drink'] != 'root beer':
                                    valid = False

                            # Clue 7: Colonial is not in house 4
                            if solution['4']['HouseStyle'] == 'colonial':
                                valid = False

                            # Clue 8: Bird is in house 4
                            if solution['4']['Animal'] != 'bird':
                                valid = False

                            # Clue 9: Tea drinker is Bob
                            for house in houses:
                                if solution[house]['Drink'] == 'tea' and solution[house]['Name'] != 'Bob':
                                    valid = False
                                elif solution[house]['Name'] == 'Bob' and solution[house]['Drink'] != 'tea':
                                    valid = False

                            # Clue 10: Tea drinker is right of Kailyn's mother
                            tea_house = None
                            kailyn_house = None
                            for house in houses:
                                if solution[house]['Drink'] == 'tea':
                                    tea_house = int(house)
                                if solution[house]['Mother'] == 'Kailyn':
                                    kailyn_house = int(house)
                            if tea_house is not None and kailyn_house is not None:
                                if tea_house <= kailyn_house:
                                    valid = False
                            else:
                                valid = False

                            # Clue 11: Root beer lover is left of Kailyn's mother
                            root_beer_house = None
                            for house in houses:
                                if solution[house]['Drink'] == 'root beer':
                                    root_beer_house = int(house)
                            if root_beer_house is not None and kailyn_house is not None:
                                if root_beer_house >= kailyn_house:
                                    valid = False
                            else:
                                valid = False

                            # Clue 12: Horse keeper is in modern house
                            for house in houses:
                                if solution[house]['Animal'] == 'horse' and solution[house]['HouseStyle'] != 'modern':
                                    valid = False
                                elif solution[house]['HouseStyle'] == 'modern' and solution[house]['Animal'] != 'horse':
                                    valid = False

                            # Clue 13: iPhone 13 user likes milk
                            for house in houses:
                                if solution[house]['PhoneModel'] == 'iphone 13' and solution[house]['Drink'] != 'milk':
                                    valid = False
                                elif solution[house]['Drink'] == 'milk' and solution[house]['PhoneModel'] != 'iphone 13':
                                    valid = False

                            # Clue 14: Dog owner likes milk
                            for house in houses:
                                if solution[house]['Animal'] == 'dog' and solution[house]['Drink'] != 'milk':
                                    valid = False
                                elif solution[house]['Drink'] == 'milk' and solution[house]['Animal'] != 'dog':
                                    valid = False

                            # Clue 15: Google Pixel 6 is in craftsman house
                            for house in houses:
                                if solution[house]['PhoneModel'] == 'google pixel 6' and solution[house]['HouseStyle'] != 'craftsman':
                                    valid = False
                                elif solution[house]['HouseStyle'] == 'craftsman' and solution[house]['PhoneModel'] != 'google pixel 6':
                                    valid = False

                            # Clue 16: Eric is not in house 2
                            if solution['2']['Name'] == 'Eric':
                                valid = False

                            # Clue 17: Tea drinker is in house 4
                            if solution['4']['Drink'] != 'tea':
                                valid = False

                            # Clue 18: Horse is in house 3
                            if solution['3']['Animal'] != 'horse':
                                valid = False

                            # Clue 19: Modern house has mother Penny
                            for house in houses:
                                if solution[house]['HouseStyle'] == 'modern' and solution[house]['Mother'] != 'Penny':
                                    valid = False
                                elif solution[house]['Mother'] == 'Penny' and solution[house]['HouseStyle'] != 'modern':
                                    valid = False

                            # Clue 20: Root beer lover is Peter
                            for house in houses:
                                if solution[house]['Drink'] == 'root beer' and solution[house]['Name'] != 'Peter':
                                    valid = False
                                elif solution[house]['Name'] == 'Peter' and solution[house]['Drink'] != 'root beer':
                                    valid = False

                            # Clue 21: Aniya is not mother in house 4
                            if solution['4']['Mother'] == 'Aniya':
                                valid = False

                            # Clue 22: Janelle is mother of water drinker (Alice)
                            for house in houses:
                                if solution[house]['Name'] == 'Alice' and solution[house]['Mother'] != 'Janelle':
                                    valid = False
                                elif solution[house]['Mother'] == 'Janelle' and solution[house]['Name'] != 'Alice':
                                    valid = False

                            if valid:
                                # Prepare the output
                                output = {
                                    "solution": {
                                        "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                                        "rows": []
                                    }
                                }
                                for house in houses:
                                    row = [house]
                                    row.append(solution[house]['Name'])
                                    row.append(solution[house]['HouseStyle'])
                                    row.append(solution[house]['Mother'])
                                    row.append(solution[house]['PhoneModel'])
                                    row.append(solution[house]['Drink'])
                                    row.append(solution[house]['Animal'])
                                    output["solution"]["rows"].append(row)
                                return json.dumps(output, indent=2)
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())