import itertools
import json

# Generate valid names permutations where Arnold is in house 4 and Peter in 5
valid_names_perms = []
for p in itertools.permutations(['Peter', 'Alice', 'Bob', 'Arnold']):
    if p[2] == 'Arnold' and p[3] == 'Peter':
        valid_names_perms.append(p)

# Generate possible birthday permutations with Feb in house 2
possible_birthdays = []
for perm in itertools.permutations(['april', 'feb', 'mar', 'jan', 'sept']):
    if perm[1] == 'feb':
        possible_birthdays.append(perm)

# Generate possible cigar permutations with Blends in house 2 and Pall Mall in 3
possible_cigars = []
for perm in itertools.permutations(['pall mall', 'prince', 'dunhill', 'blends', 'blue master']):
    if perm[1] == 'blends' and perm[2] == 'pall mall':
        possible_cigars.append(perm)

# Generate possible drink permutations with Root Beer in house 3 and Milk not in house 5
possible_drinks = []
for perm in itertools.permutations(['water', 'coffee', 'tea', 'milk', 'root beer']):
    if perm[2] == 'root beer' and perm[4] != 'milk':
        possible_drinks.append(perm)

# Iterate through all combinations
for names in valid_names_perms:
    full_names = [names[0], names[1], 'Eric', names[2], names[3]]
    bob_pos = full_names.index('Bob')
    for birthdays in possible_birthdays:
        if birthdays[bob_pos] != 'april':
            continue
        if birthdays[2] != 'jan':
            continue
        for cigars in possible_cigars:
            # Check Dunhill smoker's birthday is March
            dunhill_house = -1
            for i in range(5):
                if cigars[i] == 'dunhill':
                    dunhill_house = i
                    break
            if birthdays[dunhill_house] != 'mar':
                continue
            for drinks in possible_drinks:
                # Check Blue Master smoker drinks coffee
                blue_master_house = -1
                for i in range(5):
                    if cigars[i] == 'blue master':
                        blue_master_house = i
                        break
                if drinks[blue_master_house] != 'coffee':
                    continue
                # Check one house between tea and coffee
                tea_house = -1
                coffee_house = -1
                for i in range(5):
                    if drinks[i] == 'tea':
                        tea_house = i
                    if drinks[i] == 'coffee':
                        coffee_house = i
                if abs(tea_house - coffee_house) != 2:
                    continue
                # Build solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                        "rows": []
                    }
                }
                for house_num in range(1, 6):
                    idx = house_num - 1
                    solution["solution"]["rows"].append([
                        str(house_num),
                        full_names[idx],
                        birthdays[idx],
                        cigars[idx],
                        drinks[idx]
                    ])
                print(json.dumps(solution))
                exit()