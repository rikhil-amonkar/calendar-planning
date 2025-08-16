import json
from itertools import permutations

def solve_zebra_puzzle():
    # Define all possible categories and their options
    houses = [1, 2, 3, 4, 5]
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for animal_perm in permutations(animals):
                for nationality_perm in permutations(nationalities):
                    # Assign each permutation to houses
                    assignment = []
                    for i in range(5):
                        assignment.append({
                            'House': str(i + 1),
                            'Name': name_perm[i],
                            'Smoothie': smoothie_perm[i],
                            'Animal': animal_perm[i],
                            'Nationality': nationality_perm[i]
                        })

                    # Check all constraints
                    # Constraint 11: The person who keeps horses is in the third house.
                    if assignment[2]['Animal'] != 'horse':
                        continue

                    # Constraint 3: The Dane is the person who keeps horses.
                    if assignment[2]['Nationality'] != 'dane':
                        continue

                    # Constraint 12: The Norwegian is Alice.
                    alice_house = next((h for h in assignment if h['Name'] == 'Alice'), None)
                    if not alice_house or alice_house['Nationality'] != 'norwegian':
                        continue

                    # Constraint 6: Eric is the cat lover.
                    eric_house = next((h for h in assignment if h['Name'] == 'Eric'), None)
                    if not eric_house or eric_house['Animal'] != 'cat':
                        continue

                    # Constraint 4: The bird keeper is somewhere to the right of the cat lover.
                    cat_house = next((h for h in assignment if h['Animal'] == 'cat'), None)
                    bird_house = next((h for h in assignment if h['Animal'] == 'bird'), None)
                    if not cat_house or not bird_house or int(bird_house['House']) <= int(cat_house['House']):
                        continue

                    # Constraint 7: Bob is the bird keeper.
                    bob_house = next((h for h in assignment if h['Name'] == 'Bob'), None)
                    if not bob_house or bob_house['Animal'] != 'bird':
                        continue

                    # Constraint 9: The bird keeper is the Watermelon smoothie lover.
                    if bob_house['Smoothie'] != 'watermelon':
                        continue

                    # Constraint 10: The Desert smoothie lover is the dog owner.
                    desert_house = next((h for h in assignment if h['Smoothie'] == 'desert'), None)
                    if not desert_house or desert_house['Animal'] != 'dog':
                        continue

                    # Constraint 1: The Swedish person is directly left of the dog owner.
                    swede_house = next((h for h in assignment if h['Nationality'] == 'swede'), None)
                    dog_house = desert_house
                    if not swede_house or int(swede_house['House']) + 1 != int(dog_house['House']):
                        continue

                    # Constraint 2: There are two houses between the dog owner and the British person.
                    brit_house = next((h for h in assignment if h['Nationality'] == 'brit'), None)
                    if not brit_house or int(brit_house['House']) - int(dog_house['House']) != 3:
                        continue

                    # Constraint 5: The dog owner is directly left of the person who drinks Lime smoothies.
                    lime_house = next((h for h in assignment if h['Smoothie'] == 'lime'), None)
                    if not lime_house or int(lime_house['House']) - int(dog_house['House']) != 1:
                        continue

                    # Constraint 8: The person who likes Cherry smoothies is directly left of Peter.
                    cherry_house = next((h for h in assignment if h['Smoothie'] == 'cherry'), None)
                    peter_house = next((h for h in assignment if h['Name'] == 'Peter'), None)
                    if not cherry_house or not peter_house or int(peter_house['House']) - int(cherry_house['House']) != 1:
                        continue

                    # All constraints satisfied, prepare the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                            "rows": []
                        }
                    }
                    for house in assignment:
                        solution["solution"]["rows"].append([
                            house['House'],
                            house['Name'],
                            house['Smoothie'],
                            house['Animal'],
                            house['Nationality']
                        ])
                    return solution

    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_zebra_puzzle()
    print(json.dumps(solution, indent=2))