import itertools
import json

# Define the possible values
names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
cars = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

# Fixed positions for cars
cars_fixed = {3: 'ford f150', 5: 'toyota camry'}

# Fixed positions for mothers
mothers_fixed = {3: 'Sarah', 5: 'Kailyn'}

# Generate all possible car permutations with fixed positions
valid_cars = []
for car_perm in itertools.permutations(cars):
    valid = True
    for idx, fixed_val in cars_fixed.items():
        if car_perm[idx] != fixed_val:
            valid = False
            break
    if valid:
        valid_cars.append(car_perm)

# Generate all possible mother permutations with fixed positions
valid_mothers = []
for mother_perm in itertools.permutations(mothers):
    valid = True
    for idx, fixed_val in mothers_fixed.items():
        if mother_perm[idx] != fixed_val:
            valid = False
            break
    if valid:
        valid_mothers.append(mother_perm)

# Now, for each combination of car, mother, name, hobby permutations, check all constraints
solution_found = None

for car_perm in valid_cars:
    # Find indices for BMW and Honda
    try:
        bmw_idx = car_perm.index('bmw 3 series')
        honda_idx = car_perm.index('honda civic')
    except ValueError:
        continue  # Skip if not found

    # Remaining names excluding Bob and Arnold
    remaining_names = [n for n in names if n not in ['Bob', 'Arnold']]

    # Remaining positions for names
    remaining_positions = [i for i in range(6) if i not in {bmw_idx, honda_idx}]

    # Generate name permutations
    for name_perm in itertools.permutations(remaining_names):
        full_name = [''] * 6
        full_name[bmw_idx] = 'Bob'
        full_name[honda_idx] = 'Arnold'
        for i, pos in enumerate(remaining_positions):
            full_name[pos] = name_perm[i]

        # Determine Carol and Eric positions for hobbies
        try:
            carol_idx = full_name.index('Carol')
            eric_idx = full_name.index('Eric')
        except ValueError:
            continue  # Skip if not found

        # Remaining hobbies excluding Carol's and Eric's
        remaining_hobbies = [h for h in hobbies if h not in ['photography', 'gardening']]

        # Remaining positions for hobbies
        remaining_hobby_positions = [i for i in range(6) if i not in {carol_idx, eric_idx}]

        # Generate hobby permutations
        for hobby_perm in itertools.permutations(remaining_hobbies):
            full_hobby = [''] * 6
            full_hobby[carol_idx] = 'photography'
            full_hobby[eric_idx] = 'gardening'
            for i, pos in enumerate(remaining_hobby_positions):
                full_hobby[pos] = hobby_perm[i]

            # Check each mother permutation
            for mother_perm in valid_mothers:
                # Check clue 3: Chevrolet owner's mother is Aniya
                chev_idx = car_perm.index('chevrolet silverado') if 'chevrolet silverado' in car_perm else -1
                if chev_idx != -1 and mother_perm[chev_idx] != 'Aniya':
                    continue

                # Check clue 4: Chevrolet not in house 2 (index 1)
                if chev_idx == 1:
                    continue

                # Check clue 8: Eric directly left of knitting
                eric_pos = full_name.index('Eric')
                if eric_pos + 1 >= 6 or full_hobby[eric_pos + 1] != 'knitting':
                    continue

                # Check clue 17: Mother Holly is directly left of knitting
                knitting_pos = eric_pos + 1
                if mother_perm[eric_pos] != 'Holly':
                    continue

                # Check clue 10: Mother Penny is to the right of knitting
                penny_idx = mother_perm.index('Penny')
                if penny_idx < knitting_pos:
                    continue

                # Check clue 11: Mother Aniya is to the right of Honda Civic
                honda_civic_idx = car_perm.index('honda civic')
                aniya_idx = mother_perm.index('Aniya')
                if aniya_idx <= honda_civic_idx:
                    continue

                # Check clue 12: Alice is to the right of Ford (index 3)
                alice_idx = full_name.index('Alice')
                if alice_idx <= 3:
                    continue

                # Check clue 14: Woodworking is to the left of knitting
                woodworking_idx = full_hobby.index('woodworking')
                if woodworking_idx >= knitting_pos:
                    continue

                # Check clue 15: One house between Sarah (index 3) and cooking
                cooking_idx = full_hobby.index('cooking')
                if abs((cooking_idx + 1) - 4) != 2:
                    continue

                # If all clues are satisfied
                solution = {
                    "solution": {
                        "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                        "rows": []
                    }
                }
                for i in range(6):
                    house_num = i + 1
                    solution["solution"]["rows"].append([
                        str(house_num),
                        full_name[i],
                        car_perm[i],
                        mother_perm[i],
                        full_hobby[i]
                    ])
                print(json.dumps(solution))
                exit()

print("No solution found.")