import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
    mothers = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
    pets = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']

    # We'll represent each house as a dictionary with keys: name, mother, pet
    solution = []

    # Generate all possible permutations and check constraints
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for pet_perm in permutations(pets):
                assignment = []
                for i in range(6):
                    assignment.append({
                        'House': str(i+1),
                        'Name': name_perm[i],
                        'Mother': mother_perm[i],
                        'Pet': pet_perm[i]
                    })

                # Check all constraints
                valid = True

                # Constraint 1: Bob is not in the second house
                if assignment[1]['Name'] == 'Bob':
                    valid = False

                # Constraint 2: Two houses between cat and rabbit
                cat_houses = [h for h in assignment if h['Pet'] == 'cat']
                rabbit_houses = [h for h in assignment if h['Pet'] == 'rabbit']
                if len(cat_houses) != 1 or len(rabbit_houses) != 1:
                    valid = False
                else:
                    cat_pos = int(cat_houses[0]['House'])
                    rabbit_pos = int(rabbit_houses[0]['House'])
                    if abs(cat_pos - rabbit_pos) != 3:
                        valid = False

                # Constraint 3: Cat is directly left of mother Holly
                if valid:
                    cat_pos = None
                    holly_pos = None
                    for h in assignment:
                        if h['Pet'] == 'cat':
                            cat_pos = int(h['House'])
                        if h['Mother'] == 'Holly':
                            holly_pos = int(h['House'])
                    if cat_pos is None or holly_pos is None or (cat_pos + 1) != holly_pos:
                        valid = False

                # Constraint 4: Hamster is directly left of rabbit
                if valid:
                    hamster_pos = None
                    rabbit_pos = None
                    for h in assignment:
                        if h['Pet'] == 'hamster':
                            hamster_pos = int(h['House'])
                        if h['Pet'] == 'rabbit':
                            rabbit_pos = int(h['House'])
                    if hamster_pos is None or rabbit_pos is None or (hamster_pos + 1) != rabbit_pos:
                        valid = False

                # Constraint 5: Rabbit owner is Eric
                if valid:
                    rabbit_owner = next((h for h in assignment if h['Pet'] == 'rabbit'), None)
                    if rabbit_owner is None or rabbit_owner['Name'] != 'Eric':
                        valid = False

                # Constraint 6: One house between dog and cat
                if valid:
                    dog_pos = None
                    cat_pos = None
                    for h in assignment:
                        if h['Pet'] == 'dog':
                            dog_pos = int(h['House'])
                        if h['Pet'] == 'cat':
                            cat_pos = int(h['House'])
                    if dog_pos is None or cat_pos is None or abs(dog_pos - cat_pos) != 2:
                        valid = False

                # Constraint 7: Cat owner's mother is Janelle
                if valid:
                    cat_owner = next((h for h in assignment if h['Pet'] == 'cat'), None)
                    if cat_owner is None or cat_owner['Mother'] != 'Janelle':
                        valid = False

                # Constraint 8: Alice is directly left of Carol
                if valid:
                    alice_pos = None
                    carol_pos = None
                    for h in assignment:
                        if h['Name'] == 'Alice':
                            alice_pos = int(h['House'])
                        if h['Name'] == 'Carol':
                            carol_pos = int(h['House'])
                    if alice_pos is None or carol_pos is None or (alice_pos + 1) != carol_pos:
                        valid = False

                # Constraint 9: Carol's mother is Aniya
                if valid:
                    carol = next((h for h in assignment if h['Name'] == 'Carol'), None)
                    if carol is None or carol['Mother'] != 'Aniya':
                        valid = False

                # Constraint 10: Arnold has a cat
                if valid:
                    arnold = next((h for h in assignment if h['Name'] == 'Arnold'), None)
                    if arnold is None or arnold['Pet'] != 'cat':
                        valid = False

                # Constraint 11: Rabbit owner's mother is Kailyn
                if valid:
                    rabbit_owner = next((h for h in assignment if h['Pet'] == 'rabbit'), None)
                    if rabbit_owner is None or rabbit_owner['Mother'] != 'Kailyn':
                        valid = False

                # Constraint 12: Fish owner's mother is Sarah
                if valid:
                    fish_owner = next((h for h in assignment if h['Pet'] == 'fish'), None)
                    if fish_owner is None or fish_owner['Mother'] != 'Sarah':
                        valid = False

                if valid:
                    solution = assignment
                    break
            if solution:
                break
        if solution:
            break

    # Prepare the output in the required format
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": []
        }
    }

    for house in solution:
        output["solution"]["rows"].append([
            house["House"],
            house["Name"],
            house["Mother"],
            house["Pet"]
        ])

    return json.dumps(output, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())