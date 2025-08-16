from z3 import Solver, Int, Distinct, And, Or, Abs
import json

def solve_puzzle():
    # Constants and mappings
    HOUSES = 4
    NAMES = ["Peter", "Arnold", "Eric", "Alice"]
    PETS = ["bird", "fish", "dog", "cat"]

    PETER, ARNOLD, ERIC, ALICE = 0, 1, 2, 3
    BIRD, FISH, DOG, CAT = 0, 1, 2, 3

    # Variables: for each house (0..3 => houses 1..4), assign a Name and a Pet
    Name = [Int(f"Name_{i}") for i in range(HOUSES)]
    Pet = [Int(f"Pet_{i}") for i in range(HOUSES)]

    s = Solver()

    # Domains: each entry is one of the 4 enumerated values
    for i in range(HOUSES):
        s.add(Name[i] >= 0, Name[i] < 4)
        s.add(Pet[i] >= 0, Pet[i] < 4)

    # Uniqueness: each name appears exactly once; each pet appears exactly once
    s.add(Distinct(Name))
    s.add(Distinct(Pet))

    # Clue 1: The person who owns a dog is somewhere to the right of Alice.
    s.add(Or([
        And(Name[i] == ALICE,
            Or([And(Pet[j] == DOG, j > i) for j in range(HOUSES)]))
        for i in range(HOUSES)
    ]))

    # Clue 2: Eric is not in the first house.
    s.add(Name[0] != ERIC)

    # Clue 3: Eric is the person who keeps a pet bird.
    s.add(Or([And(Name[i] == ERIC, Pet[i] == BIRD) for i in range(HOUSES)]))

    # Clue 4: There is one house between the person with fish and Peter.
    s.add(Or([
        And(Name[i] == PETER,
            Or([And(Pet[j] == FISH, Abs(i - j) == 2) for j in range(HOUSES)]))
        for i in range(HOUSES)
    ]))

    # Clue 5: Alice is not in the first house.
    s.add(Name[0] != ALICE)

    # Clue 6: Arnold is the person with fish.
    s.add(Or([And(Name[i] == ARNOLD, Pet[i] == FISH) for i in range(HOUSES)]))

    if s.check() !=  sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build the result rows in order of houses 1..4 (indices 0..3)
    rows = []
    for i in range(HOUSES):
        name_idx = m.evaluate(Name[i]).as_long()
        pet_idx = m.evaluate(Pet[i]).as_long()
        rows.append([str(i + 1), NAMES[name_idx], PETS[pet_idx]])

    result = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()