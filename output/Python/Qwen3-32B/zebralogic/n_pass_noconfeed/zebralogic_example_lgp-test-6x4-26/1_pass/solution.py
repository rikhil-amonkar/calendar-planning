import itertools
import json

# Initialize the houses with known values
houses = [
    {'number': 1, 'Name': None, 'Pet': None, 'HouseStyle': None, 'Birthday': 'feb'},
    {'number': 2, 'Name': 'Peter', 'Pet': None, 'HouseStyle': 'colonial', 'Birthday': 'may'},
    {'number': 3, 'Name': 'Carol', 'Pet': 'bird', 'HouseStyle': 'victorian', 'Birthday': 'mar'},
    {'number': 4, 'Name': 'Arnold', 'Pet': 'dog', 'HouseStyle': 'craftsman', 'Birthday': 'jan'},
    {'number': 5, 'Name': None, 'Pet': None, 'HouseStyle': 'modern', 'Birthday': 'april'},
    {'number': 6, 'Name': 'Eric', 'Pet': None, 'HouseStyle': 'ranch', 'Birthday': 'sept'},
]

# Assign remaining HouseStyles based on deductions
houses[0]['HouseStyle'] = 'mediterranean'

# Generate possible name assignments for houses 1 and 5 (Bob and Alice)
possible_names = [
    {'house1': 'Bob', 'house5': 'Alice'},
    {'house1': 'Alice', 'house5': 'Bob'}
]

# Generate valid pet permutations for houses 1, 2, 5 (cat, rabbit, fish; fish not in house 2)
pets = ['cat', 'rabbit', 'fish']
valid_pet_perms = []
for perm in itertools.permutations(pets):
    if perm[1] != 'fish':  # house 2 (index 1) cannot have fish
        valid_pet_perms.append(perm)

# Check all combinations of names and pets
for name_assign in possible_names:
    for pet_assign in valid_pet_perms:
        # Assign names
        houses[0]['Name'] = name_assign['house1']
        houses[4]['Name'] = name_assign['house5']
        
        # Assign pets
        houses[0]['Pet'] = pet_assign[0]
        houses[1]['Pet'] = pet_assign[1]
        houses[4]['Pet'] = pet_assign[2]
        
        # Check clue 9: one house between cat and victorian (house 3)
        cat_house = None
        for h in houses:
            if h['Pet'] == 'cat':
                cat_house = h['number']
                break
        if abs(cat_house - 3) != 2:
            continue
        
        # Check clue 7: fish is to the right of Bob
        bob_house = None
        fish_house = None
        for h in houses:
            if h['Name'] == 'Bob':
                bob_house = h['number']
            if h['Pet'] == 'fish':
                fish_house = h['number']
        if fish_house <= bob_house:
            continue
        
        # Construct the solution JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                "rows": []
            }
        }
        for house in houses:
            row = [
                str(house['number']),
                house['Name'],
                house['Pet'],
                house['HouseStyle'],
                house['Birthday']
            ]
            solution['solution']['rows'].append(row)
        
        # Output the JSON
        print(json.dumps(solution, indent=2))
        exit()

print("No solution found")