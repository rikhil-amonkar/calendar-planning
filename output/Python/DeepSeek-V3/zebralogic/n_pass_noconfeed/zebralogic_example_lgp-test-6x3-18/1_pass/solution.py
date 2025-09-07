import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
    mothers = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
    pets = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for pet_perm in permutations(pets):
                # Create assignment dictionaries
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'Name': name_perm[i],
                        'Mother': mother_perm[i],
                        'Pet': pet_perm[i]
                    }
                
                # Check all constraints
                valid = True
                
                # Clue 1: Bob is not in the second house.
                if assignment[2]['Name'] == 'Bob':
                    valid = False
                    continue
                
                # Clue 2: There are two houses between the person who has a cat and the person who owns a rabbit.
                cat_house = None
                rabbit_house = None
                for house in houses:
                    if assignment[house]['Pet'] == 'cat':
                        cat_house = house
                    if assignment[house]['Pet'] == 'rabbit':
                        rabbit_house = house
                if cat_house is None or rabbit_house is None or abs(cat_house - rabbit_house) != 3:
                    valid = False
                    continue
                
                # Clue 3: The person who has a cat is directly left of The person whose mother's name is Holly.
                if cat_house is not None:
                    holly_house = None
                    for house in houses:
                        if assignment[house]['Mother'] == 'Holly':
                            holly_house = house
                    if holly_house is None or holly_house != cat_house + 1:
                        valid = False
                        continue
                
                # Clue 4: The person with a pet hamster is directly left of the person who owns a rabbit.
                hamster_house = None
                for house in houses:
                    if assignment[house]['Pet'] == 'hamster':
                        hamster_house = house
                if hamster_house is None or rabbit_house is None or hamster_house != rabbit_house - 1:
                    valid = False
                    continue
                
                # Clue 5: The person who owns a rabbit is Eric.
                if rabbit_house is not None and assignment[rabbit_house]['Name'] != 'Eric':
                    valid = False
                    continue
                
                # Clue 6: There is one house between the person who owns a dog and the person who has a cat.
                dog_house = None
                for house in houses:
                    if assignment[house]['Pet'] == 'dog':
                        dog_house = house
                if dog_house is None or cat_house is None or abs(dog_house - cat_house) != 2:
                    valid = False
                    continue
                
                # Clue 7: The person who has a cat is The person whose mother's name is Janelle.
                if cat_house is not None and assignment[cat_house]['Mother'] != 'Janelle':
                    valid = False
                    continue
                
                # Clue 8: Alice is directly left of Carol.
                alice_house = None
                carol_house = None
                for house in houses:
                    if assignment[house]['Name'] == 'Alice':
                        alice_house = house
                    if assignment[house]['Name'] == 'Carol':
                        carol_house = house
                if alice_house is None or carol_house is None or carol_house != alice_house + 1:
                    valid = False
                    continue
                
                # Clue 9: Carol is The person whose mother's name is Aniya.
                if carol_house is not None and assignment[carol_house]['Mother'] != 'Aniya':
                    valid = False
                    continue
                
                # Clue 10: Arnold is the person who has a cat.
                if cat_house is not None and assignment[cat_house]['Name'] != 'Arnold':
                    valid = False
                    continue
                
                # Clue 11: The person whose mother's name is Kailyn is the person who owns a rabbit.
                if rabbit_house is not None and assignment[rabbit_house]['Mother'] != 'Kailyn':
                    valid = False
                    continue
                
                # Clue 12: The person with an aquarium of fish is The person whose mother's name is Sarah.
                fish_house = None
                for house in houses:
                    if assignment[house]['Pet'] == 'fish':
                        fish_house = house
                if fish_house is not None:
                    sarah_house = None
                    for house in houses:
                        if assignment[house]['Mother'] == 'Sarah':
                            sarah_house = house
                    if sarah_house is None or fish_house != sarah_house:
                        valid = False
                        continue
                
                if valid:
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Pet"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['Name'],
                            assignment[house]['Mother'],
                            assignment[house]['Pet']
                        ]
                        solution["solution"]["rows"].append(row)
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    print('{"solution": {"header": ["House", "Name", "Mother", "Pet"], "rows": []}}')

if __name__ == "__main__":
    main()