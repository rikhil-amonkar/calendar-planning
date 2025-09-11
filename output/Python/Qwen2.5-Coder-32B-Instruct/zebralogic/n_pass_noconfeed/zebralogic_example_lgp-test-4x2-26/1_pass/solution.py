import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ['Arnold', 'Eric', 'Peter', 'Alice']
    occupations = ['doctor', 'engineer', 'artist', 'teacher']
    
    # Generate all possible permutations for names and occupations
    permutations = list(itertools.permutations(names))
    occupation_permutations = list(itertools.permutations(occupations))
    
    # Iterate over all combinations of name and occupation permutations
    for name_order in permutations:
        for occupation_order in occupation_permutations:
            # Create a dictionary to map house number to attributes
            house_attributes = {
                1: {'name': name_order[0], 'occupation': occupation_order[0]},
                2: {'name': name_order[1], 'occupation': occupation_order[1]},
                3: {'name': name_order[2], 'occupation': occupation_order[2]},
                4: {'name': name_order[3], 'occupation': occupation_order[3]}
            }
            
            # Check clue 2: The person who is a teacher is Peter.
            if not any(house['name'] == 'Peter' and house['occupation'] == 'teacher' for house in house_attributes.values()):
                continue
            
            # Check clue 3: Peter is not in the first house.
            if house_attributes[1]['name'] == 'Peter':
                continue
            
            # Check clue 1: There are two houses between Eric and Peter.
            eric_house = next(i for i, house in house_attributes.items() if house['name'] == 'Eric')
            peter_house = next(i for i, house in house_attributes.items() if house['name'] == 'Peter')
            if abs(eric_house - peter_house) != 3:
                continue
            
            # Check clue 5: The person who is an artist is Alice.
            if not any(house['name'] == 'Alice' and house['occupation'] == 'artist' for house in house_attributes.values()):
                continue
            
            # Check clue 4: There is one house between the person who is a doctor and Alice.
            doctor_house = next(i for i, house in house_attributes.items() if house['occupation'] == 'doctor')
            alice_house = next(i for i, house in house_attributes.items() if house['name'] == 'Alice')
            if abs(doctor_house - alice_house) != 2:
                continue
            
            # If all clues are satisfied, format the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Occupation"],
                    "rows": [
                        [str(house), house_attributes[house]['name'], house_attributes[house]['occupation']]
                        for house in range(1, 5)
                    ]
                }
            }
            
            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()