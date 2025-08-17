import itertools
import json

def solve_puzzle():
    # Initialize the solution with fixed values
    solution = [{} for _ in range(6)]  # indexes 0-5 for houses 1-6

    # Assign fixed values
    # House 2 (index 1)
    solution[1]['Name'] = 'Peter'
    solution[1]['HouseStyle'] = 'colonial'
    solution[1]['Birthday'] = 'may'

    # House 3 (index 2)
    solution[2]['Name'] = 'Carol'
    solution[2]['Birthday'] = 'mar'

    # House 4 (index 3)
    solution[3]['HouseStyle'] = 'craftsman'
    solution[3]['Name'] = 'Arnold'
    solution[3]['Pet'] = 'dog'

    # House 6 (index 5)
    solution[5]['Name'] = 'Eric'
    solution[5]['Pet'] = 'hamster'

    # Possible remaining names for houses 0 (1) and 4 (5): Bob, Alice
    name_candidates = ['Bob', 'Alice']
    name_perms = list(itertools.permutations(name_candidates))

    # Possible remaining pets for houses 0 (1), 1 (2), 4 (5): cat, rabbit, fish
    pet_candidates = ['cat', 'rabbit', 'fish']
    pet_perms = list(itertools.permutations(pet_candidates))

    # Possible remaining house styles for houses 0 (1), 4 (5), 5 (6): ranch, modern, mediterranean
    # But house 5 (index 5) cannot be mediterranean
    housestyle_candidates = ['ranch', 'modern', 'mediterranean']
    housestyle_perms = list(itertools.permutations(housestyle_candidates))
    filtered_housestyle_perms = [p for p in housestyle_perms if p[2] != 'mediterranean']

    # Possible remaining birthdays for houses 0 (1), 3 (4), 4 (5), 5 (6): jan, feb, april, sept
    birthday_candidates = ['jan', 'feb', 'april', 'sept']
    birthday_perms = list(itertools.permutations(birthday_candidates))

    # Iterate through all combinations
    for name_p in name_perms:
        solution[0]['Name'] = name_p[0]
        solution[4]['Name'] = name_p[1]

        for pet_p in pet_perms:
            solution[0]['Pet'] = pet_p[0]
            solution[1]['Pet'] = pet_p[1]
            solution[4]['Pet'] = pet_p[2]

            # Check clue 13: fish not in house 2 (index 1)
            if solution[1]['Pet'] == 'fish':
                continue

            for hsp in filtered_housestyle_perms:
                solution[0]['HouseStyle'] = hsp[0]
                solution[4]['HouseStyle'] = hsp[1]
                solution[5]['HouseStyle'] = hsp[2]

                for bday_p in birthday_perms:
                    solution[0]['Birthday'] = bday_p[0]
                    solution[3]['Birthday'] = bday_p[1]  # house 4 (index 3)
                    solution[4]['Birthday'] = bday_p[2]  # house 5 (index 4)
                    solution[5]['Birthday'] = bday_p[3]  # house 6 (index 5)

                    # Check clue 15: jan directly left of april
                    jan_pos = -1
                    april_pos = -1
                    for i in range(6):
                        if solution[i]['Birthday'] == 'jan':
                            jan_pos = i
                        if solution[i]['Birthday'] == 'april':
                            april_pos = i
                    if jan_pos != -1 and april_pos != -1 and (april_pos == jan_pos + 1):
                        pass
                    else:
                        continue

                    # Check clue 2: jan is left of sept
                    jan_pos = -1
                    sept_pos = -1
                    for i in range(6):
                        if solution[i]['Birthday'] == 'jan':
                            jan_pos = i
                        if solution[i]['Birthday'] == 'sept':
                            sept_pos = i
                    if jan_pos == -1 or sept_pos == -1 or not (jan_pos < sept_pos):
                        continue

                    # Check clue 7: fish is to the right of Bob
                    bob_house = -1
                    fish_house = -1
                    for i in range(6):
                        if solution[i]['Name'] == 'Bob':
                            bob_house = i
                        if solution[i]['Pet'] == 'fish':
                            fish_house = i
                    if bob_house == -1 or fish_house == -1 or not (fish_house > bob_house):
                        continue

                    # If all checks passed, return the solution
                    return {
                        "solution": {
                            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                            "rows": [
                                [
                                    str(i+1),
                                    solution[i].get('Name', ''),
                                    solution[i].get('Pet', ''),
                                    solution[i].get('HouseStyle', ''),
                                    solution[i].get('Birthday', '')
                                ] for i in range(6)
                            ]
                        }
                    }

    # If no solution found
    return {"solution": None}

# Convert to JSON and print
result = solve_puzzle()
print(json.dumps(result, indent=2))