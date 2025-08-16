import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
    mothers = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
    pets = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']

    # Initialize possibilities
    for name_order in permutations(names):
        for mother_order in permutations(mothers):
            for pet_order in permutations(pets):
                solution = {
                    1: {'Name': None, 'Mother': None, 'Pet': None},
                    2: {'Name': None, 'Mother': None, 'Pet': None},
                    3: {'Name': None, 'Mother': None, 'Pet': None},
                    4: {'Name': None, 'Mother': None, 'Pet': None},
                    5: {'Name': None, 'Mother': None, 'Pet': None},
                    6: {'Name': None, 'Mother': None, 'Pet': None}
                }
                
                # Assign names
                for i in range(6):
                    solution[i+1]['Name'] = name_order[i]
                
                # Assign mothers
                for i in range(6):
                    solution[i+1]['Mother'] = mother_order[i]
                
                # Assign pets
                for i in range(6):
                    solution[i+1]['Pet'] = pet_order[i]
                
                # Check constraints
                valid = True
                
                # Constraint 1: Bob is not in the second house.
                if solution[2]['Name'] == 'Bob':
                    valid = False
                
                # Constraint 2: Two houses between cat and rabbit
                cat_house = None
                rabbit_house = None
                for house in solution:
                    if solution[house]['Pet'] == 'cat':
                        cat_house = house
                    if solution[house]['Pet'] == 'rabbit':
                        rabbit_house = house
                if cat_house is None or rabbit_house is None or abs(rabbit_house - cat_house) != 3:
                    valid = False
                
                # Constraint 3: Cat is directly left of mother Holly
                if cat_house is not None and (cat_house + 1 > 6 or solution[cat_house + 1]['Mother'] != 'Holly'):
                    valid = False
                
                # Constraint 4: Hamster is directly left of rabbit
                hamster_house = None
                for house in solution:
                    if solution[house]['Pet'] == 'hamster':
                        hamster_house = house
                if hamster_house is None or rabbit_house is None or hamster_house + 1 != rabbit_house:
                    valid = False
                
                # Constraint 5: Rabbit owner is Eric
                if rabbit_house is not None and solution[rabbit_house]['Name'] != 'Eric':
                    valid = False
                
                # Constraint 6: One house between dog and cat
                dog_house = None
                for house in solution:
                    if solution[house]['Pet'] == 'dog':
                        dog_house = house
                if dog_house is None or cat_house is None or abs(dog_house - cat_house) != 2:
                    valid = False
                
                # Constraint 7: Cat owner's mother is Janelle
                if cat_house is not None and solution[cat_house]['Mother'] != 'Janelle':
                    valid = False
                
                # Constraint 8: Alice is directly left of Carol
                alice_house = None
                carol_house = None
                for house in solution:
                    if solution[house]['Name'] == 'Alice':
                        alice_house = house
                    if solution[house]['Name'] == 'Carol':
                        carol_house = house
                if alice_house is None or carol_house is None or alice_house + 1 != carol_house:
                    valid = False
                
                # Constraint 9: Carol's mother is Aniya
                if carol_house is not None and solution[carol_house]['Mother'] != 'Aniya':
                    valid = False
                
                # Constraint 10: Arnold has a cat
                arnold_house = None
                for house in solution:
                    if solution[house]['Name'] == 'Arnold':
                        arnold_house = house
                if arnold_house is None or solution[arnold_house]['Pet'] != 'cat':
                    valid = False
                
                # Constraint 11: Rabbit owner's mother is Kailyn
                if rabbit_house is not None and solution[rabbit_house]['Mother'] != 'Kailyn':
                    valid = False
                
                # Constraint 12: Fish owner's mother is Sarah
                fish_house = None
                for house in solution:
                    if solution[house]['Pet'] == 'fish':
                        fish_house = house
                if fish_house is not None and solution[fish_house]['Mother'] != 'Sarah':
                    valid = False
                
                if valid:
                    # Prepare the output
                    output = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Pet"],
                            "rows": []
                        }
                    }
                    for house in sorted(solution.keys()):
                        row = [
                            str(house),
                            solution[house]['Name'],
                            solution[house]['Mother'],
                            solution[house]['Pet']
                        ]
                        output["solution"]["rows"].append(row)
                    return json.dumps(output, indent=2)
    
    return json.dumps({"solution": {"header": ["House", "Name", "Mother", "Pet"], "rows": []}})

print(solve_puzzle())