import itertools
import json

def solve_puzzle():
    # Define the categories and their possible values
    names = ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice']
    house_styles = ['modern', 'craftsman', 'ranch', 'victorian', 'colonial']
    mothers = ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya']
    phone_models = ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21']
    drinks = ['coffee', 'water', 'root beer', 'tea', 'milk']
    animals = ['fish', 'dog', 'horse', 'bird', 'cat']

    # Generate valid permutations for each category with fixed positions
    valid_names_perms = []
    for p in itertools.permutations(names):
        if p[3] == 'Bob':  # Bob is in house 4 (index 3)
            valid_names_perms.append(p)

    valid_drinks_perms = []
    for p in itertools.permutations(drinks):
        if p[3] == 'tea':  # tea in house 4
            valid_drinks_perms.append(p)

    valid_animal_perms = []
    for p in itertools.permutations(animals):
        if p[2] == 'horse' and p[3] == 'bird':  # house 3 has horse, house 4 has bird
            valid_animal_perms.append(p)

    valid_phone_perms = []
    for p in itertools.permutations(phone_models):
        if p[2] == 'oneplus 9':  # house 3 has oneplus 9
            valid_phone_perms.append(p)

    valid_house_style_perms = []
    for p in itertools.permutations(house_styles):
        if p[2] == 'modern':  # house 3 has modern style
            valid_house_style_perms.append(p)

    valid_mother_perms = []
    for p in itertools.permutations(mothers):
        if p[2] == 'Penny':  # house 3's mother is Penny
            valid_mother_perms.append(p)

    def check_constraints(houses):
        # Clue 1: Google Pixel 6 not in first house.
        if any(h['House'] == 1 and h['PhoneModel'] == 'google pixel 6' for h in houses):
            return False

        # Clue 2: Alice drinks water.
        if not any(h['Name'] == 'Alice' and h['Drink'] == 'water' for h in houses):
            return False

        # Clue 3: Colonial is to the right of huawei p50 user.
        colonial_pos = None
        huawei_pos = None
        for i, h in enumerate(houses):
            if h['HouseStyle'] == 'colonial':
                colonial_pos = i
            if h['PhoneModel'] == 'huawei p50':
                huawei_pos = i
        if colonial_pos is not None and huawei_pos is not None and colonial_pos <= huawei_pos:
            return False

        # Clue 4: Horses keeper uses OnePlus 9.
        if not all(h['PhoneModel'] == 'oneplus 9' for h in houses if h['Animal'] == 'horse'):
            return False

        # Clue 5: Ranch-style has mother Kailyn.
        if not all(h['Mother'] == 'Kailyn' for h in houses if h['HouseStyle'] == 'ranch'):
            return False

        # Clue 6: Root beer lover is cat lover.
        if not all(h['Animal'] == 'cat' for h in houses if h['Drink'] == 'root beer'):
            return False

        # Clue 7: Colonial not in fourth house.
        if any(h['HouseStyle'] == 'colonial' and h['House'] == 4 for h in houses):
            return False

        # Clue 8: Bird keeper in fourth house.
        if not any(h['House'] == 4 and h['Animal'] == 'bird' for h in houses):
            return False

        # Clue 9: Bob drinks tea.
        if not any(h['Name'] == 'Bob' and h['Drink'] == 'tea' for h in houses):
            return False

        # Clue 10: Tea drinker is to the right of Kailyn's mother.
        kailyn_mother_pos = None
        tea_drinker_pos = None
        for i, h in enumerate(houses):
            if h['Mother'] == 'Kailyn':
                kailyn_mother_pos = h['House']
            if h['Drink'] == 'tea':
                tea_drinker_pos = h['House']
        if kailyn_mother_pos is not None and tea_drinker_pos is not None and tea_drinker_pos <= kailyn_mother_pos:
            return False

        # Clue 11: Root beer lover is left of Kailyn's mother.
        root_beer_pos = None
        for h in houses:
            if h['Drink'] == 'root beer':
                root_beer_pos = h['House']
        if root_beer_pos is not None and kailyn_mother_pos is not None and root_beer_pos >= kailyn_mother_pos:
            return False

        # Clue 12: Horses keeper is in modern-style house.
        if not all(h['HouseStyle'] == 'modern' for h in houses if h['Animal'] == 'horse'):
            return False

        # Clue 13: iPhone 13 user drinks milk.
        if not all(h['Drink'] == 'milk' for h in houses if h['PhoneModel'] == 'iphone 13'):
            return False

        # Clue 14: Dog owner drinks milk.
        if not all(h['Drink'] == 'milk' for h in houses if h['Animal'] == 'dog'):
            return False

        # Clue 15: Google Pixel 6 in Craftsman-style.
        if not all(h['HouseStyle'] == 'craftsman' for h in houses if h['PhoneModel'] == 'google pixel 6'):
            return False

        # Clue 16: Eric not in second house.
        if any(h['House'] == 2 and h['Name'] == 'Eric' for h in houses):
            return False

        # Clue 17: Tea in fourth house.
        if not any(h['House'] == 4 and h['Drink'] == 'tea' for h in houses):
            return False

        # Clue 18: Horses in third house.
        if not any(h['House'] == 3 and h['Animal'] == 'horse' for h in houses):
            return False

        # Clue 19: Modern-style mother is Penny.
        if not all(h['Mother'] == 'Penny' for h in houses if h['HouseStyle'] == 'modern'):
            return False

        # Clue 20: Root beer lover is Peter.
        if not all(h['Name'] == 'Peter' for h in houses if h['Drink'] == 'root beer'):
            return False

        # Clue 21: Aniya's mother not in fourth house.
        if any(h['House'] == 4 and h['Mother'] == 'Aniya' for h in houses):
            return False

        # Clue 22: Janelle's mother is the one who drinks water.
        if not all(h['Drink'] == 'water' for h in houses if h['Mother'] == 'Janelle'):
            return False

        return True

    def output_json(houses):
        header = ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"]
        rows = []
        for h in houses:
            row = [
                str(h['House']),
                h['Name'],
                h['HouseStyle'],
                h['Mother'],
                h['PhoneModel'],
                h['Drink'],
                h['Animal']
            ]
            rows.append(row)
        solution = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))

    # Iterate through all combinations of valid permutations
    for names_p in valid_names_perms:
        for drinks_p in valid_drinks_perms:
            for animal_p in valid_animal_perms:
                for phone_p in valid_phone_perms:
                    for house_style_p in valid_house_style_perms:
                        for mother_p in valid_mother_perms:
                            houses = []
                            for i in range(5):
                                house = {
                                    'House': i + 1,
                                    'Name': names_p[i],
                                    'HouseStyle': house_style_p[i],
                                    'Mother': mother_p[i],
                                    'PhoneModel': phone_p[i],
                                    'Drink': drinks_p[i],
                                    'Animal': animal_p[i],
                                }
                                houses.append(house)
                            if check_constraints(houses):
                                output_json(houses)
                                return

solve_puzzle()