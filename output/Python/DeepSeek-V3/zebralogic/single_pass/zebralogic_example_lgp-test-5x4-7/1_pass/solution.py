import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']
    
    # We'll represent each house as a dictionary with the categories as keys
    # Initialize all possibilities
    for name_order in permutations(names):
        for smoothie_order in permutations(smoothies):
            for animal_order in permutations(animals):
                for nationality_order in permutations(nationalities):
                    # Create a list of houses with current permutation
                    solution = []
                    for i in range(5):
                        house = {
                            'House': str(i+1),
                            'Name': name_order[i],
                            'smoothie': smoothie_order[i],
                            'animal': animal_order[i],
                            'nationality': nationality_order[i]
                        }
                        solution.append(house)
                    
                    # Check all constraints
                    valid = True
                    
                    # Constraint 11: The person who keeps horses is in the third house.
                    if solution[2]['animal'] != 'horse':
                        valid = False
                        continue
                    
                    # Constraint 3: The Dane is the person who keeps horses.
                    if solution[2]['nationality'] != 'dane':
                        valid = False
                        continue
                    
                    # Constraint 12: The Norwegian is Alice.
                    alice_house = None
                    for house in solution:
                        if house['Name'] == 'Alice':
                            alice_house = house
                            break
                    if alice_house is None or alice_house['nationality'] != 'norwegian':
                        valid = False
                        continue
                    
                    # Constraint 6: Eric is the cat lover.
                    eric_house = None
                    for house in solution:
                        if house['Name'] == 'Eric':
                            eric_house = house
                            break
                    if eric_house is None or eric_house['animal'] != 'cat':
                        valid = False
                        continue
                    
                    # Constraint 7: Bob is the bird keeper.
                    bob_house = None
                    for house in solution:
                        if house['Name'] == 'Bob':
                            bob_house = house
                            break
                    if bob_house is None or bob_house['animal'] != 'bird':
                        valid = False
                        continue
                    
                    # Constraint 9: The bird keeper is the Watermelon smoothie lover.
                    if bob_house['smoothie'] != 'watermelon':
                        valid = False
                        continue
                    
                    # Constraint 4: The bird keeper is somewhere to the right of the cat lover.
                    if int(bob_house['House']) <= int(eric_house['House']):
                        valid = False
                        continue
                    
                    # Find the dog owner
                    dog_owner = None
                    for house in solution:
                        if house['animal'] == 'dog':
                            dog_owner = house
                            break
                    if dog_owner is None:
                        valid = False
                        continue
                    
                    # Constraint 10: The Desert smoothie lover is the dog owner.
                    if dog_owner['smoothie'] != 'desert':
                        valid = False
                        continue
                    
                    # Constraint 1: The Swedish person is directly left of the dog owner.
                    swede_house = None
                    for house in solution:
                        if house['nationality'] == 'swede':
                            swede_house = house
                            break
                    if swede_house is None or int(swede_house['House']) != int(dog_owner['House']) - 1:
                        valid = False
                        continue
                    
                    # Constraint 2: There are two houses between the dog owner and the British person.
                    brit_house = None
                    for house in solution:
                        if house['nationality'] == 'brit':
                            brit_house = house
                            break
                    if brit_house is None or abs(int(dog_owner['House']) - int(brit_house['House'])) != 3:
                        valid = False
                        continue
                    
                    # Constraint 5: The dog owner is directly left of the person who drinks Lime smoothies.
                    lime_house = None
                    for house in solution:
                        if house['smoothie'] == 'lime':
                            lime_house = house
                            break
                    if lime_house is None or int(lime_house['House']) != int(dog_owner['House']) + 1:
                        valid = False
                        continue
                    
                    # Constraint 8: The person who likes Cherry smoothies is directly left of Peter.
                    peter_house = None
                    for house in solution:
                        if house['Name'] == 'Peter':
                            peter_house = house
                            break
                    if peter_house is None:
                        valid = False
                        continue
                    
                    cherry_house = None
                    for house in solution:
                        if house['smoothie'] == 'cherry':
                            cherry_house = house
                            break
                    if cherry_house is None or int(cherry_house['House']) != int(peter_house['House']) - 1:
                        valid = False
                        continue
                    
                    # If all constraints are satisfied, return the solution
                    if valid:
                        # Prepare the output in the required format
                        output = {
                            "solution": {
                                "header": ["House", "Name", "smoothie", "animal", "nationality"],
                                "rows": []
                            }
                        }
                        for house in solution:
                            row = [
                                house['House'],
                                house['Name'],
                                house['smoothie'],
                                house['animal'],
                                house['nationality']
                            ]
                            output["solution"]["rows"].append(row)
                        return output
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result as JSON
solution = solve_puzzle()
print(json.dumps(solution, indent=2))