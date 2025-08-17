import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice']
    house_styles = ['modern', 'craftsman', 'ranch', 'victorian', 'colonial']
    mothers = ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya']
    phones = ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21']
    drinks = ['coffee', 'water', 'root beer', 'tea', 'milk']
    animals = ['fish', 'dog', 'horse', 'bird', 'cat']

    # Generate constrained permutations
    animal_perms = []
    for p in itertools.permutations(animals):
        if p[2] == 'horse' and p[3] == 'bird':
            animal_perms.append(p)

    hs_perms = []
    for p in itertools.permutations(house_styles):
        if p[2] == 'modern':
            hs_perms.append(p)

    phone_perms = []
    for p in itertools.permutations(phones):
        if p[2] == 'oneplus 9':
            phone_perms.append(p)

    drink_perms = []
    for p in itertools.permutations(drinks):
        if p[3] == 'tea':
            drink_perms.append(p)

    name_perms = []
    for p in itertools.permutations(names):
        if p[3] == 'Bob':
            name_perms.append(p)

    mother_perms = []
    for p in itertools.permutations(mothers):
        if p[2] == 'Penny':
            mother_perms.append(p)

    def check_constraints(houses):
        # Clue 1: Google Pixel 6 not in first house.
        if houses[0]['PhoneModel'] == 'google pixel 6':
            return False

        # Clue 3: Colonial is to the right of huawei p50.
        colonial_pos = None
        huawei_pos = None
        for i in range(5):
            if houses[i]['HouseStyle'] == 'colonial':
                colonial_pos = i
            if houses[i]['PhoneModel'] == 'huawei p50':
                huawei_pos = i
        if colonial_pos is not None and huawei_pos is not None:
            if colonial_pos <= huawei_pos:
                return False
        else:
            return False  # assuming they should exist

        # Clue 5: Ranch-style house has mother Kailyn.
        ranch_pos = None
        for i in range(5):
            if houses[i]['HouseStyle'] == 'ranch':
                ranch_pos = i
                if houses[i]['Mother'] != 'Kailyn':
                    return False
        if ranch_pos is None:
            return False

        # Clue 7: Colonial not in fourth house.
        if houses[3]['HouseStyle'] == 'colonial':
            return False

        # Clue 10: Tea drinker (house 4, index 3) is to the right of Kailyn's mother (ranch-style house).
        if ranch_pos >= 3:
            return False

        # Clue 11: Root beer lover is to the left of Kailyn's mother (ranch_pos)
        root_beer_pos = None
        for i in range(5):
            if houses[i]['Drink'] == 'root beer':
                root_beer_pos = i
                break
        if root_beer_pos is None:
            return False
        if root_beer_pos >= ranch_pos:
            return False

        # Clue 13: iPhone 13 user likes milk.
        for i in range(5):
            if houses[i]['PhoneModel'] == 'iphone 13':
                if houses[i]['Drink'] != 'milk':
                    return False
                break
        else:
            return False  # no iphone 13?

        # Clue 14: Dog owner likes milk.
        dog_pos = None
        for i in range(5):
            if houses[i]['Animal'] == 'dog':
                dog_pos = i
                if houses[i]['Drink'] != 'milk':
                    return False
                break
        if dog_pos is None:
            return False

        # Clue 15: Google Pixel 6 is in craftsman-style house.
        for i in range(5):
            if houses[i]['PhoneModel'] == 'google pixel 6':
                if houses[i]['HouseStyle'] != 'craftsman':
                    return False
                break
        else:
            return False  # no google pixel 6?

        # Clue 16: Eric is not in the second house (index 1).
        if houses[1]['Name'] == 'Eric':
            return False

        # Clue 20: Root beer lover is Peter.
        if houses[root_beer_pos]['Name'] != 'Peter':
            return False

        # Clue 21: Aniya not in fourth house (index 3).
        if houses[3]['Mother'] == 'Aniya':
            return False

        return True

    for names_p in name_perms:
        for mothers_p in mother_perms:
            for hs_p in hs_perms:
                for phones_p in phone_perms:
                    for drinks_p in drink_perms:
                        for animals_p in animal_perms:
                            houses = []
                            for i in range(5):
                                house = {
                                    'Name': names_p[i],
                                    'HouseStyle': hs_p[i],
                                    'Mother': mothers_p[i],
                                    'PhoneModel': phones_p[i],
                                    'Drink': drinks_p[i],
                                    'Animal': animals_p[i]
                                }
                                houses.append(house)
                            if check_constraints(houses):
                                # Check if Alice's drink is water and mother is Janelle
                                alice_ok = False
                                for i in range(5):
                                    if houses[i]['Name'] == 'Alice':
                                        if houses[i]['Drink'] == 'water' and houses[i]['Mother'] == 'Janelle':
                                            alice_ok = True
                                            break
                                if not alice_ok:
                                    continue
                                # Check if root beer lover is cat owner
                                root_beer_pos = None
                                for i in range(5):
                                    if houses[i]['Drink'] == 'root beer':
                                        root_beer_pos = i
                                        break
                                if houses[root_beer_pos]['Animal'] != 'cat':
                                    continue
                                # All checks passed
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                                        "rows": []
                                    }
                                }
                                for i in range(5):
                                    house_num = str(i + 1)
                                    row = [
                                        house_num,
                                        houses[i]['Name'],
                                        houses[i]['HouseStyle'],
                                        houses[i]['Mother'],
                                        houses[i]['PhoneModel'],
                                        houses[i]['Drink'],
                                        houses[i]['Animal']
                                    ]
                                    solution['solution']['rows'].append(row)
                                print(json.dumps(solution))
                                return

if __name__ == "__main__":
    main()