import json
from itertools import permutations

def solve_puzzle():
    houses = list(range(5))  # indices 0..4 represent houses 1..5

    # Categories
    Names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    Foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
    Cars = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
    Phones = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
    Occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
    Drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']

    solutions = []

    # Name placements with Eric fixed at house 4 (index 3)
    fixed_index_for_eric = 3
    others = ['Peter', 'Arnold', 'Alice', 'Bob']
    free_indices = [0, 1, 2, 4]

    for perm_names in permutations(others):
        name_at = [None] * 5
        name_at[fixed_index_for_eric] = 'Eric'
        for idx, house_idx in enumerate(free_indices):
            name_at[house_idx] = perm_names[idx]

        pos_name = {n: i for i, n in enumerate(name_at)}

        # Clue 2 implies Peter cannot be in the first house (no one to the left for milk)
        if pos_name['Peter'] == 0:
            continue

        # Food permutations with constraints
        for perm_food in permutations(Foods):
            # Enforce: Alice loves stir fry
            if perm_food[pos_name['Alice']] != 'stir fry':
                continue
            # Enforce: Peter loves grilled cheese
            if perm_food[pos_name['Peter']] != 'grilled cheese':
                continue

            food_at = list(perm_food)
            pos_food = {f: i for i, f in enumerate(food_at)}

            # Clue 2: milk is directly left of grilled cheese -> implies grilled cheese not in house 1 (index 0)
            if pos_food['grilled cheese'] == 0:
                continue

            # Car permutations with constraints
            for perm_car in permutations(Cars):
                car_at = list(perm_car)
                pos_car = {c: i for i, c in enumerate(car_at)}

                # Clue 16: Arnold owns a Toyota Camry
                if pos_car['toyota camry'] != pos_name['Arnold']:
                    continue

                # Clue 15: One house between Alice and Ford F-150
                if abs(pos_car['ford f150'] - pos_name['Alice']) != 2:
                    continue

                # Clue 12: Honda Civic is directly left of the spaghetti eater
                if not (pos_car['honda civic'] + 1 == pos_food['spaghetti']):
                    continue

                # Phones: construct with constraints, only 2 options for remaining two phones
                # Initialize phone assignments
                for leftover_assignment in permutations(['google pixel 6', 'huawei p50']):
                    phone_at = [None] * 5

                    # Clue 3: Alice uses Samsung Galaxy S21
                    pos_alice = pos_name['Alice']
                    if phone_at[pos_alice] is not None:
                        continue
                    phone_at[pos_alice] = 'samsung galaxy s21'

                    # Clue 11 and 18: Doctor (Arnold) is directly left of OnePlus 9 user (who is a lawyer)
                    pos_arnold = pos_name['Arnold']
                    if pos_arnold == 4:
                        continue  # cannot be left of someone if in last house (though Eric is fixed at 4)
                    if phone_at[pos_arnold + 1] is not None and phone_at[pos_arnold + 1] != 'oneplus 9':
                        continue
                    # If Alice is at pos_arnold+1, conflict since she already has S21
                    if pos_alice == pos_arnold + 1:
                        continue
                    phone_at[pos_arnold + 1] = 'oneplus 9'

                    # Clue 10: Stew eater uses iPhone 13
                    pos_stew = pos_food['stew']
                    if phone_at[pos_stew] is not None and phone_at[pos_stew] != 'iphone 13':
                        continue
                    # If stew house equals oneplus or s21 already assigned, ensure consistency
                    if phone_at[pos_stew] is None:
                        phone_at[pos_stew] = 'iphone 13'
                    elif phone_at[pos_stew] != 'iphone 13':
                        continue

                    # Fill remaining two phones with Pixel 6 and Huawei P50
                    remaining_indices = [i for i in range(5) if phone_at[i] is None]
                    if len(remaining_indices) != 2:
                        continue
                    phone_at[remaining_indices[0]] = leftover_assignment[0]
                    phone_at[remaining_indices[1]] = leftover_assignment[1]

                    pos_phone = {p: i for i, p in enumerate(phone_at)}

                    # Occupations: assign with constraints
                    occ_at = [None] * 5

                    # Clue 7: Arnold is doctor
                    occ_at[pos_name['Arnold']] = 'doctor'

                    # Clue 14: Alice is artist
                    if occ_at[pos_alice] is not None and occ_at[pos_alice] != 'artist':
                        continue
                    occ_at[pos_alice] = 'artist'

                    # Clue 18: OnePlus 9 user is lawyer
                    pos_oneplus = pos_phone['oneplus 9']
                    if occ_at[pos_oneplus] is not None and occ_at[pos_oneplus] != 'lawyer':
                        continue
                    # If Alice were at oneplus, conflict would already have rejected earlier
                    occ_at[pos_oneplus] = 'lawyer'

                    # Clue 9: Engineer owns BMW 3 Series
                    pos_bmw = pos_car['bmw 3 series']
                    if occ_at[pos_bmw] is not None and occ_at[pos_bmw] != 'engineer':
                        continue
                    occ_at[pos_bmw] = 'engineer'

                    # Fill remaining occupation as teacher
                    remaining_occ_indices = [i for i in range(5) if occ_at[i] is None]
                    if len(remaining_occ_indices) != 1:
                        continue
                    occ_at[remaining_occ_indices[0]] = 'teacher'

                    # Drinks: assign deterministically with constraints
                    drink_at = [None] * 5

                    # Clue 1: Root beer lover owns a Honda Civic
                    pos_civic = pos_car['honda civic']
                    if drink_at[pos_civic] is not None and drink_at[pos_civic] != 'root beer':
                        continue
                    drink_at[pos_civic] = 'root beer'

                    # Clue 2: Milk is directly left of grilled cheese
                    pos_grilled = pos_food['grilled cheese']
                    pos_milk = pos_grilled - 1
                    if pos_milk < 0:
                        continue
                    if drink_at[pos_milk] is not None and drink_at[pos_milk] != 'milk':
                        continue
                    drink_at[pos_milk] = 'milk'

                    # Clue 13: Google Pixel 6 user is the tea drinker
                    pos_tea = pos_phone['google pixel 6']
                    # Clue 5: Tea drinker not in fifth house (index 4)
                    if pos_tea == 4:
                        continue
                    if drink_at[pos_tea] is not None and drink_at[pos_tea] != 'tea':
                        continue
                    drink_at[pos_tea] = 'tea'

                    # Clue 8: iPhone 13 user is the coffee drinker
                    # Clue 10 already ties stew to iPhone 13; now tie to coffee
                    pos_coffee = pos_phone['iphone 13']
                    if drink_at[pos_coffee] is not None and drink_at[pos_coffee] != 'coffee':
                        continue
                    drink_at[pos_coffee] = 'coffee'

                    # Clue 6: BMW is somewhere to the left of the tea drinker
                    if pos_bmw >= pos_tea:
                        continue

                    # Check for drink collisions (no two drinks on same house)
                    assigned_drink_positions = [i for i, d in enumerate(drink_at) if d is not None]
                    if len(set(assigned_drink_positions)) != len(assigned_drink_positions):
                        continue

                    # Assign remaining drink as water
                    remaining_drink_indices = [i for i in range(5) if drink_at[i] is None]
                    if len(remaining_drink_indices) != 1:
                        continue
                    drink_at[remaining_drink_indices[0]] = 'water'

                    # All constraints should be satisfied here; compile a solution
                    # Build final rows
                    header = ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"]
                    rows = []
                    for i in range(5):
                        row = [
                            str(i + 1),
                            name_at[i],
                            food_at[i],
                            car_at[i],
                            phone_at[i],
                            occ_at[i],
                            drink_at[i],
                        ]
                        rows.append(row)

                    solution = {
                        "solution": {
                            "header": header,
                            "rows": rows
                        }
                    }
                    solutions.append(solution)

    # Prefer a unique solution; otherwise take the first found
    if not solutions:
        # In the unlikely event no solution found, return an empty structure per format
        return {
            "solution": {
                "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                "rows": []
            }
        }
    return solutions[0]

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))