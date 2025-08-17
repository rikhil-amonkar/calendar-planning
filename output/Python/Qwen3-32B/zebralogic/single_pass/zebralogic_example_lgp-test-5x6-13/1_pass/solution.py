import itertools
import json

def check_all_clues(houses):
    # Clue 1: root beer lover owns Honda Civic.
    for i in range(5):
        if houses[i]['drink'] == 'root beer' and houses[i]['car'] != 'honda civic':
            return False
        if houses[i]['car'] == 'honda civic' and houses[i]['drink'] != 'root beer':
            return False

    # Clue 2: milk drinker is directly left of grilled cheese lover.
    for i in range(4):  # i is 0-3
        if houses[i]['drink'] == 'milk' and houses[i+1]['food'] != 'grilled cheese':
            return False

    # Clue 5: Tea drinker not in fifth house.
    if houses[4]['drink'] == 'tea':
        return False

    # Clue 6: BMW 3 Series owner is to the left of tea drinker.
    tea_index = None
    for i in range(5):
        if houses[i]['drink'] == 'tea':
            tea_index = i
            break
    if tea_index is None:
        return False
    has_bmw_left = any(houses[i]['car'] == 'bmw 3 series' for i in range(tea_index))
    if not has_bmw_left:
        return False

    # Clue 8: iPhone 13 user is coffee drinker.
    for i in range(5):
        if houses[i]['phone'] == 'iphone 13' and houses[i]['drink'] != 'coffee':
            return False

    # Clue 9: Engineer owns BMW 3 series.
    for i in range(5):
        if houses[i]['occupation'] == 'engineer' and houses[i]['car'] != 'bmw 3 series':
            return False
        if houses[i]['car'] == 'bmw 3 series' and houses[i]['occupation'] != 'engineer':
            return False

    # Clue 10: Stew lover uses iPhone 13.
    for i in range(5):
        if houses[i]['food'] == 'stew' and houses[i]['phone'] != 'iphone 13':
            return False
        if houses[i]['phone'] == 'iphone 13' and houses[i]['drink'] != 'coffee':
            return False

    # Clue 11: Doctor (Arnold) is directly left of OnePlus 9 user.
    arnold_index = None
    for i in range(5):
        if houses[i]['name'] == 'Arnold':
            arnold_index = i
            break
    if arnold_index is None:
        return False
    if arnold_index + 1 >= 5 or houses[arnold_index + 1]['phone'] != 'oneplus 9':
        return False

    # Clue 12: Honda Civic owner is directly left of spaghetti eater.
    for i in range(4):
        if houses[i]['car'] == 'honda civic' and houses[i+1]['food'] != 'spaghetti':
            return False

    # Clue 13: Google Pixel 6 user is tea drinker.
    for i in range(5):
        if houses[i]['phone'] == 'google pixel 6' and houses[i]['drink'] != 'tea':
            return False

    # Clue 15: One house between Alice and Ford F-150 owner.
    alice_index = None
    for i in range(5):
        if houses[i]['name'] == 'Alice':
            alice_index = i
            break
    if alice_index is None:
        return False
    ford_index = None
    for i in range(5):
        if houses[i]['car'] == 'ford f150':
            ford_index = i
            break
    if ford_index is None:
        return False
    if abs(alice_index - ford_index) != 2:
        return False

    # Clue 18: OnePlus 9 user is lawyer.
    for i in range(5):
        if houses[i]['phone'] == 'oneplus 9' and houses[i]['occupation'] != 'lawyer':
            return False

    return True

def output_solution(houses):
    header = ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"]
    rows = []
    for i in range(5):
        house_num = str(i+1)
        row = [
            house_num,
            houses[i]['name'],
            houses[i]['food'],
            houses[i]['car'],
            houses[i]['phone'],
            houses[i]['occupation'],
            houses[i]['drink']
        ]
        rows.append(row)
    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))

def main():
    all_names = ['Arnold', 'Alice', 'Peter', 'Bob', 'Eric']
    possible_name_perms = []
    for p in itertools.permutations(['Arnold', 'Alice', 'Peter', 'Bob']):
        temp = [None] * 5
        temp[0] = p[0]
        temp[1] = p[1]
        temp[2] = p[2]
        temp[4] = p[3]
        temp[3] = 'Eric'
        possible_name_perms.append(temp)

    for name_perm in possible_name_perms:
        # Initialize houses with known attributes
        houses = [{'name': name_perm[i], 'food': None, 'car': None, 'phone': None, 'occupation': None, 'drink': None} for i in range(5)]
        for i in range(5):
            if houses[i]['name'] == 'Arnold':
                houses[i]['occupation'] = 'doctor'
                houses[i]['car'] = 'toyota camry'
            elif houses[i]['name'] == 'Alice':
                houses[i]['food'] = 'stir fry'
                houses[i]['phone'] = 'samsung galaxy s21'
                houses[i]['occupation'] = 'artist'
            elif houses[i]['name'] == 'Peter':
                houses[i]['food'] = 'grilled cheese'

        # Food
        fixed_food = {}
        for i in range(5):
            if houses[i]['food'] is not None:
                fixed_food[i] = houses[i]['food']
        remaining_foods = [f for f in ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza'] if f not in fixed_food.values()]
        variable_food_houses = [i for i in range(5) if houses[i]['food'] is None]
        food_perms = list(itertools.permutations(remaining_foods))

        # Car
        fixed_car = {}
        for i in range(5):
            if houses[i]['car'] is not None:
                fixed_car[i] = houses[i]['car']
        remaining_cars = [c for c in ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic'] if c not in fixed_car.values()]
        variable_car_houses = [i for i in range(5) if houses[i]['car'] is None]
        car_perms = list(itertools.permutations(remaining_cars))

        # Phone
        fixed_phone = {}
        for i in range(5):
            if houses[i]['phone'] is not None:
                fixed_phone[i] = houses[i]['phone']
        remaining_phones = [p for p in ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50'] if p not in fixed_phone.values()]
        variable_phone_houses = [i for i in range(5) if houses[i]['phone'] is None]
        phone_perms = list(itertools.permutations(remaining_phones))

        # Occupation
        fixed_occupation = {}
        for i in range(5):
            if houses[i]['occupation'] is not None:
                fixed_occupation[i] = houses[i]['occupation']
        remaining_occupations = [o for o in ['teacher', 'lawyer', 'doctor', 'artist', 'engineer'] if o not in fixed_occupation.values()]
        variable_occupation_houses = [i for i in range(5) if houses[i]['occupation'] is None]
        occupation_perms = list(itertools.permutations(remaining_occupations))

        # Drink
        fixed_drink = {}
        for i in range(5):
            if houses[i]['drink'] is not None:
                fixed_drink[i] = houses[i]['drink']
        remaining_drinks = [d for d in ['tea', 'milk', 'water', 'root beer', 'coffee'] if d not in fixed_drink.values()]
        variable_drink_houses = [i for i in range(5) if houses[i]['drink'] is None]
        drink_perms = list(itertools.permutations(remaining_drinks))

        # Iterate through all combinations
        for food_p in food_perms:
            temp_food = [None]*5
            for i, val in zip(variable_food_houses, food_p):
                temp_food[i] = val

            for car_p in car_perms:
                temp_car = [None]*5
                for i, val in zip(variable_car_houses, car_p):
                    temp_car[i] = val

                for phone_p in phone_perms:
                    temp_phone = [None]*5
                    for i, val in zip(variable_phone_houses, phone_p):
                        temp_phone[i] = val

                    for occupation_p in occupation_perms:
                        temp_occupation = [None]*5
                        for i, val in zip(variable_occupation_houses, occupation_p):
                            temp_occupation[i] = val

                        for drink_p in drink_perms:
                            temp_drink = [None]*5
                            for i, val in zip(variable_drink_houses, drink_p):
                                temp_drink[i] = val

                            # Build full houses
                            full_houses = []
                            for i in range(5):
                                h = {
                                    'name': houses[i]['name'],
                                    'food': temp_food[i] if houses[i]['food'] is None else houses[i]['food'],
                                    'car': temp_car[i] if houses[i]['car'] is None else houses[i]['car'],
                                    'phone': temp_phone[i] if houses[i]['phone'] is None else houses[i]['phone'],
                                    'occupation': temp_occupation[i] if houses[i]['occupation'] is None else houses[i]['occupation'],
                                    'drink': temp_drink[i] if houses[i]['drink'] is None else houses[i]['drink'],
                                }
                                full_houses.append(h)

                            # Check all clues
                            if check_all_clues(full_houses):
                                output_solution(full_houses)
                                return

if __name__ == "__main__":
    main()