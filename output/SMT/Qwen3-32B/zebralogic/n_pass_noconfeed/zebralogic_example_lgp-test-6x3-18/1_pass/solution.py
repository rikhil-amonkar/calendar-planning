import json
from z3 import *

def main():
    s = Solver()

    # Define variables for each house (1-6)
    name_vars = [Int(f'name_{i+1}') for i in range(6)]
    mother_vars = [Int(f'mother_{i+1}') for i in range(6)]
    pet_vars = [Int(f'pet_{i+1}') for i in range(6)]

    # Constraints: all variables are between 0 and 5
    for var in name_vars + mother_vars + pet_vars:
        s.add(And(0 <= var, var <= 5))

    # All must be distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(mother_vars))
    s.add(Distinct(pet_vars))

    # Clue 1: Bob is not in the second house (Bob is index 2, house 2 is index 1)
    s.add(name_vars[1] != 2)

    # Variables for specific positions
    cat_house = Int('cat_house')
    rabbit_house = Int('rabbit_house')
    s.add(And(1 <= cat_house, cat_house <= 6))
    s.add(And(1 <= rabbit_house, rabbit_house <= 6))

    # Clue 2: Two houses between cat and rabbit
    s.add(Abs(cat_house - rabbit_house) == 3)

    # Clue 3: Cat is directly left of Holly's mother (mother in next house is Holly)
    s.add(mother_vars[cat_house] == 1)  # Holly is index 1

    # Clue 7: Cat's mother is Janelle (index 2)
    s.add(mother_vars[cat_house - 1] == 2)

    # Clue 10: Arnold is the cat owner (index 0)
    s.add(name_vars[cat_house - 1] == 0)

    # Pet constraints for cat and rabbit
    s.add(pet_vars[cat_house - 1] == 3)  # cat is index 3
    s.add(pet_vars[rabbit_house - 1] == 5)  # rabbit is index 5

    # Clue 4: Hamster directly left of rabbit
    s.add(pet_vars[rabbit_house - 2] == 0)  # hamster is index 0
    s.add(rabbit_house >= 2)  # to avoid negative index

    # Clue 5: Rabbit owner is Eric (index 1)
    s.add(name_vars[rabbit_house - 1] == 1)

    # Clue 6: One house between dog and cat
    dog_house = Int('dog_house')
    s.add(And(1 <= dog_house, dog_house <= 6))
    s.add(pet_vars[dog_house - 1] == 1)  # dog is index 1
    s.add(Abs(dog_house - cat_house) == 2)

    # Clue 8 and 9: Alice directly left of Carol, Carol's mother is Aniya (index 3)
    alice_house = Int('alice_house')
    carol_house = Int('carol_house')
    s.add(And(1 <= alice_house, alice_house <= 5))  # Carol can't be in house 6+1
    s.add(And(1 <= carol_house, carol_house <= 6))
    s.add(name_vars[alice_house - 1] == 3)  # Alice is index 3
    s.add(name_vars[carol_house - 1] == 4)  # Carol is index 4
    s.add(carol_house == alice_house + 1)
    s.add(mother_vars[carol_house - 1] == 3)  # Aniya is index 3

    # Clue 11: Rabbit's mother is Kailyn (index 5)
    s.add(mother_vars[rabbit_house - 1] == 5)

    # Clue 12: Fish owner's mother is Sarah (index 0)
    fish_house = Int('fish_house')
    s.add(And(1 <= fish_house, fish_house <= 6))
    s.add(pet_vars[fish_house - 1] == 4)  # fish is index 4
    s.add(mother_vars[fish_house - 1] == 0)

    if s.check() == sat:
        model = s.model()

        # Mapping integers to names, mothers, pets
        name_list = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
        mother_list = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
        pet_list = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']

        solution_rows = []
        for house in range(1, 7):
            name_idx = model[name_vars[house - 1]].as_long()
            mother_idx = model[mother_vars[house - 1]].as_long()
            pet_idx = model[pet_vars[house - 1]].as_long()
            solution_rows.append([
                str(house),
                name_list[name_idx],
                mother_list[mother_idx],
                pet_list[pet_idx]
            ])

        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Pet"],
                "rows": solution_rows
            }
        }

        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()