from z3 import *
import json

def main():
    solver = Solver()

    # There are 4 houses: indices 0,1,2,3 corresponding to houses 1,2,3,4.
    # For each house we have a name, hair color, and music genre.
    # We represent each attribute as an integer in {0,1,2,3}.

    # Name mapping: 0: Eric, 1: Arnold, 2: Peter, 3: Alice
    # Hair mapping: 0: blonde, 1: black, 2: brown, 3: red
    # Music mapping: 0: pop, 1: jazz, 2: rock, 3: classical

    names = [Int(f"name_{i}") for i in range(4)]
    hair = [Int(f"hair_{i}") for i in range(4)]
    music = [Int(f"music_{i}") for i in range(4)]

    # Domain constraints: each variable is in 0..3
    for i in range(4):
        solver.add(And(names[i] >= 0, names[i] < 4))
        solver.add(And(hair[i] >= 0, hair[i] < 4))
        solver.add(And(music[i] >= 0, music[i] < 4))
        
    # All attributes are distinct across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(hair))
    solver.add(Distinct(music))

    # Clue 1: Eric is the person who has red hair.
    # Enforce that if a house has Eric (0) then it must have red hair (3)
    # and if a house has red hair then it must be Eric.
    for i in range(4):
        solver.add(Implies(names[i] == 0, hair[i] == 3))
        solver.add(Implies(hair[i] == 3, names[i] == 0))

    # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
    # For houses 0,1,2: if a house has classical music (3) then the next house must have blonde hair (0).
    for i in range(3):
        solver.add(Implies(music[i] == 3, hair[i+1] == 0))

    # Clue 5: The person who loves classical music is in the first house.
    solver.add(music[0] == 3)

    # Clue 3: The person who has brown hair is not in the first house.
    solver.add(hair[0] != 2)

    # Clue 4: The person who loves pop music is not in the third house.
    # (Note: The third house is index 2.)
    solver.add(music[2] != 0)

    # Clue 6: The person who loves jazz music is the person who has red hair.
    # Enforce equivalence between jazz (1) and red hair (3) in each house.
    for i in range(4):
        solver.add(Implies(music[i] == 1, hair[i] == 3))
        solver.add(Implies(hair[i] == 3, music[i] == 1))

    # Clue 7: The person who loves rock music is Arnold.
    # Enforce equivalence between rock (2) and Arnold (1) in each house.
    for i in range(4):
        solver.add(Implies(music[i] == 2, names[i] == 1))
        solver.add(Implies(names[i] == 1, music[i] == 2))

    # Clue 8: Peter is somewhere to the right of the person who loves rock music.
    # For every pair of houses (i, j), if house i is Peter (2) and house j has rock (2) then i > j.
    for i in range(4):
        for j in range(4):
            solver.add(Implies(And(names[i] == 2, music[j] == 2), i > j))

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        names_map = ["Eric", "Arnold", "Peter", "Alice"]
        hair_map = ["blonde", "black", "brown", "red"]
        music_map = ["pop", "jazz", "rock", "classical"]

        rows = []
        # Houses are numbered 1 to 4
        for i in range(4):
            house_num = str(i + 1)
            name_val = names_map[model.evaluate(names[i]).as_long()]
            hair_val = hair_map[model.evaluate(hair[i]).as_long()]
            music_val = music_map[model.evaluate(music[i]).as_long()]
            rows.append([house_num, name_val, hair_val, music_val])
        
        output = {
            "solution": {
                "header": ["House", "Name", "HairColor", "MusicGenre"],
                "rows": rows
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": "no solution found"}))

if __name__ == "__main__":
    main()