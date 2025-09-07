import json
from itertools import permutations

def main():
    # Define all possible values
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']
    houses = [1, 2, 3, 4, 5]
    
    # Try all permutations
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for animal_perm in permutations(animals):
                for nationality_perm in permutations(nationalities):
                    # Create assignment dictionaries
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'name': name_perm[i],
                            'smoothie': smoothie_perm[i],
                            'animal': animal_perm[i],
                            'nationality': nationality_perm[i]
                        }
                    
                    # Check all constraints
                    valid = True
                    
                    # Clue 1: The Swedish person is directly left of the dog owner.
                    swede_house = None
                    dog_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'swede':
                            swede_house = house
                        if assignment[house]['animal'] == 'dog':
                            dog_house = house
                    if swede_house is None or dog_house is None or swede_house + 1 != dog_house:
                        valid = False
                    
                    # Clue 2: There are two houses between the dog owner and the British person.
                    brit_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'brit':
                            brit_house = house
                    if brit_house is None or abs(dog_house - brit_house) != 3:
                        valid = False
                    
                    # Clue 3: The Dane is the person who keeps horses.
                    dane_house = None
                    horse_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'dane':
                            dane_house = house
                        if assignment[house]['animal'] == 'horse':
                            horse_house = house
                    if dane_house is None or horse_house is None or dane_house != horse_house:
                        valid = False
                    
                    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
                    bird_house = None
                    cat_house = None
                    for house in houses:
                        if assignment[house]['animal'] == 'bird':
                            bird_house = house
                        if assignment[house]['animal'] == 'cat':
                            cat_house = house
                    if bird_house is None or cat_house is None or bird_house <= cat_house:
                        valid = False
                    
                    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
                    lime_house = None
                    for house in houses:
                        if assignment[house]['smoothie'] == 'lime':
                            lime_house = house
                    if lime_house is None or dog_house + 1 != lime_house:
                        valid = False
                    
                    # Clue 6: Eric is the cat lover.
                    eric_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Eric':
                            eric_house = house
                    if eric_house is None or eric_house != cat_house:
                        valid = False
                    
                    # Clue 7: Bob is the bird keeper.
                    bob_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Bob':
                            bob_house = house
                    if bob_house is None or bob_house != bird_house:
                        valid = False
                    
                    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
                    cherry_house = None
                    peter_house = None
                    for house in houses:
                        if assignment[house]['smoothie'] == 'cherry':
                            cherry_house = house
                        if assignment[house]['name'] == 'Peter':
                            peter_house = house
                    if cherry_house is None or peter_house is None or cherry_house + 1 != peter_house:
                        valid = False
                    
                    # Clue 9: The bird keeper is the Watermelon smoothie lover.
                    watermelon_house = None
                    for house in houses:
                        if assignment[house]['smoothie'] == 'watermelon':
                            watermelon_house = house
                    if watermelon_house is None or watermelon_house != bird_house:
                        valid = False
                    
                    # Clue 10: The Desert smoothie lover is the dog owner.
                    desert_house = None
                    for house in houses:
                        if assignment[house]['smoothie'] == 'desert':
                            desert_house = house
                    if desert_house is None or desert_house != dog_house:
                        valid = False
                    
                    # Clue 11: The person who keeps horses is in the third house.
                    if horse_house != 3:
                        valid = False
                    
                    # Clue 12: The Norwegian is Alice.
                    norwegian_house = None
                    alice_house = None
                    for house in houses:
                        if assignment[house]['nationality'] == 'norwegian':
                            norwegian_house = house
                        if assignment[house]['name'] == 'Alice':
                            alice_house = house
                    if norwegian_house is None or alice_house is None or norwegian_house != alice_house:
                        valid = False
                    
                    if valid:
                        # Prepare the solution
                        rows = []
                        for house in sorted(assignment.keys()):
                            row = [
                                str(house),
                                assignment[house]['name'],
                                assignment[house]['smoothie'],
                                assignment[house]['animal'],
                                assignment[house]['nationality']
                            ]
                            rows.append(row)
                        
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                                "rows": rows
                            }
                        }
                        
                        print(json.dumps(result, indent=2))
                        return
    
    print('{"solution": {"header": ["House", "Name", "Smoothie", "Animal", "Nationality"], "rows": []}}')

if __name__ == "__main__":
    main()