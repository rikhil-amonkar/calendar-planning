import itertools
import json

# Define all possible options for each category
names_list = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
vacations_list = ['cruise', 'city', 'camping', 'beach', 'mountain']
children_list = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
nationalities_list = ['dane', 'norwegian', 'brit', 'german', 'swede']

# Generate valid permutations with fixed constraints
valid_vacs = [p for p in itertools.permutations(vacations_list) if p[0] == 'cruise']
valid_children = [p for p in itertools.permutations(children_list) if p[3] == 'Meredith']
valid_nats = [p for p in itertools.permutations(nationalities_list) if p[4] == 'dane']
valid_names = list(itertools.permutations(names_list))

for names in valid_names:
    for vacs in valid_vacs:
        for children in valid_children:
            for nats in valid_nats:
                # Clue 1: The Norwegian is Peter
                clue1 = True
                for i in range(5):
                    if names[i] == 'Peter' and nats[i] != 'norwegian':
                        clue1 = False
                        break
                if not clue1:
                    continue

                # Clue 5: Alice is the British person
                clue5 = True
                for i in range(5):
                    if names[i] == 'Alice' and nats[i] != 'brit':
                        clue5 = False
                        break
                if not clue5:
                    continue

                # Clue 8: Eric is not in the fifth house
                if names[4] == 'Eric':
                    continue

                # Clue 11: Bob is the person who enjoys camping trips
                clue11 = True
                for i in range(5):
                    if names[i] == 'Bob' and vacs[i] != 'camping':
                        clue11 = False
                        break
                if not clue11:
                    continue

                # Clue 13: The person who enjoys camping trips is not in the fifth house
                bob_index = None
                for i in range(5):
                    if names[i] == 'Bob':
                        bob_index = i
                        break
                if bob_index == 4:
                    continue

                # Clue 2: The Swedish person's child is Bella
                clue2 = True
                for i in range(5):
                    if nats[i] == 'swede' and children[i] != 'Bella':
                        clue2 = False
                        break
                if not clue2:
                    continue

                # Clue 3: The person who loves beach vacations is directly left of the person whose child is Samantha
                clue3 = True
                beach_index = None
                for i in range(5):
                    if vacs[i] == 'beach':
                        beach_index = i
                        if i + 1 < 5 and children[i + 1] == 'Samantha':
                            break
                        else:
                            clue3 = False
                            break
                if beach_index is None or not clue3:
                    continue

                # Clue 4: The person's child is named Bella is not in the second house
                if children[1] == 'Bella':
                    continue

                # Clue 9: The Swedish person is somewhere to the right of the Norwegian
                norwegian_pos = None
                swede_pos = None
                for i in range(5):
                    if nats[i] == 'norwegian':
                        norwegian_pos = i
                    if nats[i] == 'swede':
                        swede_pos = i
                if norwegian_pos is None or swede_pos is None or swede_pos <= norwegian_pos:
                    continue

                # Clue 10: One house between the person's child is named Fred and the person who prefers city breaks
                fred_index = None
                city_index = None
                for i in range(5):
                    if children[i] == 'Fred':
                        fred_index = i
                    if vacs[i] == 'city':
                        city_index = i
                if fred_index is None or city_index is None or abs(fred_index - city_index) != 2:
                    continue

                # All constraints are satisfied, construct the solution
                solution_rows = []
                for i in range(5):
                    solution_rows.append([
                        str(i + 1),
                        names[i],
                        vacs[i],
                        children[i],
                        nats[i]
                    ])

                solution = {
                    "solution": {
                        "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(solution))
                exit()