import itertools
import json

# Define the lists
people = ['Alice', 'Peter', 'Arnold', 'Eric']
mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
flowers = ['carnations', 'roses', 'lilies', 'daffodils']

# Function to check if a given assignment satisfies all constraints
def is_valid_solution(people_order, mothers_order, flowers_order):
    # Create a dictionary for easy lookup
    house_info = {i+1: {'Name': people_order[i], 'Mother': mothers_order[i], 'Flower': flowers_order[i]} for i in range(4)}
    
    # Check each constraint
    # Constraint 1: Alice is The person whose mother's name is Kailyn.
    if house_info[3]['Name'] != 'Alice' or house_info[3]['Mother'] != 'Kailyn':
        return False
    
    # Constraint 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
    janelle_house = next(i for i in range(1, 5) if house_info[i]['Mother'] == 'Janelle')
    arnold_house = next(i for i in range(1, 5) if house_info[i]['Name'] == 'Arnold')
    if janelle_house <= arnold_house:
        return False
    
    # Constraint 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
    carnations_house = next(i for i in range(1, 5) if house_info[i]['Flower'] == 'carnations')
    peter_house = next(i for i in range(1, 5) if house_info[i]['Name'] == 'Peter')
    if peter_house <= carnations_house:
        return False
    
    # Constraint 4: Eric is the person who loves a bouquet of daffodils.
    if house_info[next(i for i in range(1, 5) if house_info[i]['Flower'] == 'daffodils')]['Name'] != 'Eric':
        return False
    
    # Constraint 5: Arnold is The person whose mother's name is Holly.
    if house_info[next(i for i in range(1, 5) if house_info[i]['Name'] == 'Arnold')]['Mother'] != 'Holly':
        return False
    
    # Constraint 6: The person who loves a carnations arrangement is somewhere to the right of The person whose mother's name is Holly.
    holly_house = next(i for i in range(1, 5) if house_info[i]['Mother'] == 'Holly')
    if carnations_house <= holly_house:
        return False
    
    # Constraint 7: The person who loves the bouquet of lilies is directly left of Alice.
    lilies_house = next(i for i in range(1, 5) if house_info[i]['Flower'] == 'lilies')
    if lilies_house + 1 != 3:
        return False
    
    # Constraint 8: Alice is in the third house.
    if house_info[3]['Name'] != 'Alice':
        return False
    
    return True

# Generate all permutations
for people_perm in itertools.permutations(people):
    for mothers_perm in itertools.permutations(mothers):
        for flowers_perm in itertools.permutations(flowers):
            if is_valid_solution(people_perm, mothers_perm, flowers_perm):
                # Construct the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Flower"],
                        "rows": [
                            [str(i), people_perm[i-1], mothers_perm[i-1], flowers_perm[i-1]] for i in range(1, 5)
                        ]
                    }
                }
                print(json.dumps(solution, indent=2))
                break