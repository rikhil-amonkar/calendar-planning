import itertools
import json

# Define the possible values for each category
names = ['Peter', 'Arnold', 'Eric']
cars = ['toyota camry', 'ford f150', 'tesla model 3']
styles = ['ranch', 'colonial', 'victorian']
pets = ['cat', 'dog', 'fish']
occupations = ['engineer', 'doctor', 'teacher']
vacations = ['city', 'mountain', 'beach']

# Generate all permutations for each category
name_perms = list(itertools.permutations(names))
car_perms = list(itertools.permutations(cars))
style_perms = list(itertools.permutations(styles))
pet_perms = list(itertools.permutations(pets))
occupation_perms = list(itertools.permutations(occupations))
vacation_perms = list(itertools.permutations(vacations))

# Generate all possible combinations of permutations
all_combinations = itertools.product(
    name_perms, car_perms, style_perms, pet_perms, occupation_perms, vacation_perms
)

for combination in all_combinations:
    names_p, cars_p, styles_p, pets_p, occupations_p, vacations_p = combination

    # Clue 1: Fish in first house
    if pets_p[0] != 'fish':
        continue

    # Clue 2: Toyota Camry in second house
    if cars_p[1] != 'toyota camry':
        continue

    # Clue 3: Mountain not in second house
    if vacations_p[1] == 'mountain':
        continue

    # Clue 4: City not in second house
    if vacations_p[1] == 'city':
        continue

    # Clue 5: Ranch is left of Peter
    ranch_index = styles_p.index('ranch')
    peter_index = names_p.index('Peter')
    if ranch_index >= peter_index:
        continue

    # Clue 6: Toyota Camry directly left of colonial
    if styles_p[1 + 1] != 'colonial':
        continue

    # Clue 7: Arnold has cat
    arnold_has_cat = True
    for i in range(3):
        if names_p[i] == 'Arnold' and pets_p[i] != 'cat':
            arnold_has_cat = False
            break
    if not arnold_has_cat:
        continue

    # Clue 8: Eric left of mountain
    eric_index = names_p.index('Eric')
    mountain_index = vacations_p.index('mountain')
    if eric_index >= mountain_index:
        continue

    # Clue 9: Engineer not in third house
    if occupations_p[2] == 'engineer':
        continue

    # Clue 10: Tesla left of teacher
    tesla_index = cars_p.index('tesla model 3')
    teacher_index = occupations_p.index('teacher')
    if tesla_index >= teacher_index:
        continue

    # Clue 11: Dog owner is engineer
    dog_engineer = True
    for i in range(3):
        if pets_p[i] == 'dog' and occupations_p[i] != 'engineer':
            dog_engineer = False
            break
    if not dog_engineer:
        continue

    # Construct the solution
    solution_rows = []
    for i in range(3):
        house = str(i + 1)
        solution_rows.append([
            house,
            names_p[i],
            cars_p[i],
            styles_p[i],
            pets_p[i],
            occupations_p[i],
            vacations_p[i]
        ])

    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": solution_rows
        }
    }

    print(json.dumps(solution))
    exit()