import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
    cars = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
    phones = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
    occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
    drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']

    def backtrack(assigned_houses, used_names, used_foods, used_cars, used_phones, used_occupations, used_drinks, pending_constraints):
        if len(assigned_houses) == 5:
            # Check remaining global constraints
            fifth_house_drink = assigned_houses[4]['Drink']
            if fifth_house_drink == 'tea':
                return None

            bmw_pos = None
            tea_pos = None
            for i, house in enumerate(assigned_houses):
                if house['CarModel'] == 'bmw 3 series':
                    bmw_pos = i
                if house['Drink'] == 'tea':
                    tea_pos = i
            if tea_pos is not None:
                if bmw_pos is None or bmw_pos >= tea_pos:
                    return None

            for house in assigned_houses:
                if house['Occupation'] == 'engineer' and house['CarModel'] != 'bmw 3 series':
                    return None

            for house in assigned_houses:
                if house['Food'] == 'stew' and house['PhoneModel'] != 'iphone 13':
                    return None

            for house in assigned_houses:
                if house['PhoneModel'] == 'iphone 13' and house['Drink'] != 'coffee':
                    return None

            for house in assigned_houses:
                if house['PhoneModel'] == 'google pixel 6' and house['Drink'] != 'tea':
                    return None

            for i in range(4):
                if assigned_houses[i]['Occupation'] == 'doctor' and assigned_houses[i+1]['PhoneModel'] != 'oneplus 9':
                    return None

            for house in assigned_houses:
                if house['PhoneModel'] == 'oneplus 9' and house['Occupation'] != 'lawyer':
                    return None

            alice_pos = None
            ford_pos = None
            for i, house in enumerate(assigned_houses):
                if house['Name'] == 'Alice':
                    alice_pos = i
                if house['CarModel'] == 'ford f150':
                    ford_pos = i
            if alice_pos is not None and ford_pos is not None and abs(alice_pos - ford_pos) != 2:
                return None

            for house in assigned_houses:
                if house['Name'] == 'Peter' and house['Food'] != 'grilled cheese':
                    return None

            return assigned_houses
        else:
            current_house_num = len(assigned_houses)
            if current_house_num == 3:
                if 'Eric' in used_names:
                    return None
                possible_names = ['Eric']
            else:
                possible_names = [n for n in names if n not in used_names]
            possible_foods = [f for f in foods if f not in used_foods]
            possible_cars = [c for c in cars if c not in used_cars]
            possible_phones = [p for p in phones if p not in used_phones]
            possible_occupations = [o for o in occupations if o not in used_occupations]
            possible_drinks = [d for d in drinks if d not in used_drinks]

            for name, food, car, phone, occupation, drink in itertools.product(possible_names, possible_foods, possible_cars, possible_phones, possible_occupations, possible_drinks):
                if name == 'Arnold':
                    if occupation != 'doctor' or car != 'toyota camry':
                        continue
                if name == 'Alice':
                    if food != 'stir fry' or phone != 'samsung galaxy s21' or occupation != 'artist':
                        continue
                if name == 'Peter':
                    if food != 'grilled cheese':
                        continue

                if drink == 'root beer' and car != 'honda civic':
                    continue
                if phone == 'iphone 13' and drink != 'coffee':
                    continue
                if food == 'stew' and phone != 'iphone 13':
                    continue
                if phone == 'google pixel 6' and drink != 'tea':
                    continue
                if occupation == 'engineer' and car != 'bmw 3 series':
                    continue

                valid = True
                for constraint in pending_constraints:
                    type_, prev_index = constraint
                    if type_ == 'honda_civic':
                        if food != 'spaghetti':
                            valid = False
                            break
                    elif type_ == 'milk':
                        if food != 'grilled cheese':
                            valid = False
                            break
                    elif type_ == 'doctor':
                        if phone != 'oneplus 9':
                            valid = False
                            break
                if not valid:
                    continue

                new_used_names = used_names.copy()
                new_used_names.add(name)
                new_used_foods = used_foods.copy()
                new_used_foods.add(food)
                new_used_cars = used_cars.copy()
                new_used_cars.add(car)
                new_used_phones = used_phones.copy()
                new_used_phones.add(phone)
                new_used_occupations = used_occupations.copy()
                new_used_occupations.add(occupation)
                new_used_drinks = used_drinks.copy()
                new_used_drinks.add(drink)

                new_pending = []
                if drink == 'milk':
                    new_pending.append(('milk', current_house_num))
                if car == 'honda civic':
                    new_pending.append(('honda_civic', current_house_num))
                if occupation == 'doctor':
                    new_pending.append(('doctor', current_house_num))

                result = backtrack(
                    assigned_houses + [{'Name': name, 'Food': food, 'CarModel': car, 'PhoneModel': phone, 'Occupation': occupation, 'Drink': drink}],
                    new_used_names, new_used_foods, new_used_cars, new_used_phones, new_used_occupations, new_used_drinks,
                    new_pending
                )
                if result is not None:
                    return result
            return None

    solution = backtrack([], set(), set(), set(), set(), set(), set(), [])
    if solution is None:
        return None

    header = ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"]
    rows = []
    for i, house in enumerate(solution, 1):
        row = [
            str(i),
            house['Name'],
            house['Food'],
            house['CarModel'],
            house['PhoneModel'],
            house['Occupation'],
            house['Drink']
        ]
        rows.append(row)

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))