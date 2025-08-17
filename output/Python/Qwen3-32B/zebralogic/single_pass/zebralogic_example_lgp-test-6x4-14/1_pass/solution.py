import itertools
import json

names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
car_models = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']

for perm in itertools.permutations(names):
    # Check Arnold and Bob positions (not in house 4 or 6)
    if perm[3] == 'Arnold' or perm[5] == 'Arnold':
        continue
    if perm[3] == 'Bob' or perm[5] == 'Bob':
        continue

    # Assign known cars
    cars = [None] * 6
    cars[3] = 'ford f150'  # House 4
    cars[5] = 'toyota camry'  # House 6

    arnold_index = perm.index('Arnold')
    bob_index = perm.index('Bob')
    cars[arnold_index] = 'honda civic'
    cars[bob_index] = 'bmw 3 series'

    assigned_car_indices = {3, 5, arnold_index, bob_index}
    remaining_indices = [i for i in range(6) if i not in assigned_car_indices]

    remaining_cars = []
    for cm in car_models:
        if cm not in [cars[3], cars[5], cars[arnold_index], cars[bob_index]]:
            remaining_cars.append(cm)

    for car_perm in itertools.permutations(remaining_cars):
        temp_cars = cars.copy()
        for i, idx in enumerate(remaining_indices):
            temp_cars[idx] = car_perm[i]

        chev_index = temp_cars.index('chevrolet silverado')
        if chev_index == 1:  # House 2
            continue
        if chev_index <= arnold_index:
            continue

        # Assign mothers
        mothers_list = [None] * 6
        mothers_list[5] = 'Kailyn'
        mothers_list[3] = 'Sarah'
        mothers_list[chev_index] = 'Aniya'

        assigned_mother_indices = {5, 3, chev_index}
        remaining_mother_indices = [i for i in range(6) if i not in assigned_mother_indices]
        remaining_mothers = ['Penny', 'Holly', 'Janelle']

        for mother_perm in itertools.permutations(remaining_mothers):
            temp_mothers = mothers_list.copy()
            for i, idx in enumerate(remaining_mother_indices):
                temp_mothers[idx] = mother_perm[i]

            # Assign hobbies
            hobbies_list = [None] * 6
            carol_index = perm.index('Carol')
            hobbies_list[carol_index] = 'photography'

            eric_index = perm.index('Eric')
            hobbies_list[eric_index] = 'gardening'

            assigned_hobby_indices = {carol_index, eric_index}
            remaining_hobby_indices = [i for i in range(6) if i not in assigned_hobby_indices]
            remaining_hobbies = ['cooking', 'knitting', 'woodworking', 'painting']

            for hobby_perm in itertools.permutations(remaining_hobbies):
                temp_hobbies = hobbies_list.copy()
                for i, idx in enumerate(remaining_hobby_indices):
                    temp_hobbies[idx] = hobby_perm[i]

                knitting_index = temp_hobbies.index('knitting')
                if knitting_index != eric_index + 1:
                    continue

                woodworking_index = temp_hobbies.index('woodworking')
                if woodworking_index >= knitting_index:
                    continue

                cooking_index = temp_hobbies.index('cooking')
                if cooking_index not in [1, 5]:
                    continue

                holly_mother_index = temp_mothers.index('Holly')
                if holly_mother_index + 1 != knitting_index:
                    continue

                penny_mother_index = temp_mothers.index('Penny')
                if penny_mother_index <= knitting_index:
                    continue

                solution_rows = []
                for i in range(6):
                    house_num = i + 1
                    name = perm[i]
                    car = temp_cars[i]
                    mother = temp_mothers[i]
                    hobby = temp_hobbies[i]
                    solution_rows.append([str(house_num), name, car, mother, hobby])

                json_output = {
                    "solution": {
                        "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(json_output, indent=2))
                exit()