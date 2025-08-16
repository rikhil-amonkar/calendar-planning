from z3 import *
import json

def solve():
    s = Solver()

    # Define variables for each house (1-6)
    names = [Int(f'name_{h}') for h in range(1, 7)]
    mothers = [Int(f'mother_{h}') for h in range(1, 7)]
    pets = [Int(f'pet_{h}') for h in range(1, 7)]

    # Add range and distinct constraints
    for var in names + mothers + pets:
        s.add(And(0 <= var, var <= 5))
    s.add(Distinct(names))
    s.add(Distinct(mothers))
    s.add(Distinct(pets))

    # Clue 1: Bob is not in the second house
    s.add(names[1] != 2)

    # Clue 5: The person who owns a rabbit is Eric
    for i in range(6):
        s.add(Implies(pets[i] == 5, names[i] == 1))

    # Clue 11: The person whose mother is Kailyn owns the rabbit
    for i in range(6):
        s.add(Implies(mothers[i] == 5, pets[i] == 5))

    # Clue 10: Arnold has the cat
    for i in range(6):
        s.add(Implies(names[i] == 0, pets[i] == 3))

    # Clue 7: The person who owns a cat has a mother named Janelle
    for i in range(6):
        s.add(Implies(pets[i] == 3, mothers[i] == 2))

    # Clue 3: The person with a cat is directly left of the person whose mother is Holly
    cat_house = Int('cat_house')
    s.add(And(1 <= cat_house, cat_house <= 5))
    s.add(pets[cat_house - 1] == 3)
    s.add(mothers[cat_house] == 1)

    # Clue 2: Two houses between the cat and the rabbit
    rabbit_house = Int('rabbit_house')
    s.add(And(1 <= rabbit_house, rabbit_house <= 6))
    s.add(pets[rabbit_house - 1] == 5)
    s.add(Abs(cat_house - rabbit_house) == 3)

    # Clue 4: Hamster is directly left of the rabbit
    for i in range(5):
        s.add(Implies(pets[i] == 0, pets[i + 1] == 5))

    # Clue 6: One house between the dog and the cat
    dog_house = Int('dog_house')
    s.add(And(1 <= dog_house, dog_house <= 6))
    s.add(pets[dog_house - 1] == 1)
    s.add(Abs(dog_house - cat_house) == 2)

    # Clue 8 and 9: Alice is directly left of Carol, and Carol's mother is Aniya
    alice_house = Int('alice_house')
    carol_house = Int('carol_house')
    s.add(And(1 <= alice_house, alice_house <= 6))
    s.add(And(1 <= carol_house, carol_house <= 6))
    s.add(names[alice_house - 1] == 3)
    s.add(names[carol_house - 1] == 4)
    s.add(carol_house == alice_house + 1)
    s.add(mothers[carol_house - 1] == 3)

    # Clue 12: The person with a fish has a mother named Sarah
    for i in range(6):
        s.add(Implies(pets[i] == 4, mothers[i] == 0))

    if s.check() == sat:
        model = s.model()

        # Mapping for names
        name_map = {0: 'Arnold', 1: 'Eric', 2: 'Bob', 3: 'Alice', 4: 'Carol', 5: 'Peter'}
        # Mapping for mothers
        mother_map = {0: 'Sarah', 1: 'Holly', 2: 'Janelle', 3: 'Aniya', 4: 'Penny', 5: 'Kailyn'}
        # Mapping for pets
        pet_map = {0: 'hamster', 1: 'dog', 2: 'bird', 3: 'cat', 4: 'fish', 5: 'rabbit'}

        solution = []
        for h in range(1, 7):
            i = h - 1
            name_val = model.eval(names[i]).as_long()
            mother_val = model.eval(mothers[i]).as_long()
            pet_val = model.eval(pets[i]).as_long()
            solution.append([str(h), name_map[name_val], mother_map[mother_val], pet_map[pet_val]])

        return {
            "solution": {
                "header": ["House", "Name", "Mother", "Pet"],
                "rows": solution
            }
        }
    else:
        return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))