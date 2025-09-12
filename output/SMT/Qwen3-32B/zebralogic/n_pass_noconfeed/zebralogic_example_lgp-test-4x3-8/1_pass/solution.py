import json
from z3 import *

def main():
    solver = Solver()

    name = IntVector('name', 4)
    hair = IntVector('hair', 4)
    music = IntVector('music', 4)

    # All values in each category are distinct
    solver.add(Distinct(name))
    solver.add(Distinct(hair))
    solver.add(Distinct(music))

    # All variables are between 0 and 3
    for i in range(4):
        solver.add(And(0 <= name[i], name[i] <= 3))
        solver.add(And(0 <= hair[i], hair[i] <= 3))
        solver.add(And(0 <= music[i], music[i] <= 3))

    # Clue 1: Eric (name 0) has red hair (hair 3)
    for i in range(4):
        solver.add(Or(name[i] != 0, hair[i] == 3))

    # Clue 5: classical (music 3) in first house (index 0)
    solver.add(music[0] == 3)

    # Clue 2: classical is directly left of blonde hair. Since clue 5 fixes music[0] to 3, this means hair[1] must be 0 (blonde)
    solver.add(hair[1] == 0)

    # Clue 3: brown hair (hair 2) not in first house (hair[0] != 2)
    solver.add(hair[0] != 2)

    # Clue 4: pop music (music 0) not in third house (index 2)
    solver.add(music[2] != 0)

    # Clue 6: jazz (music 1) has red hair (hair 3)
    solver.add(Or(
        And(music[0] == 1, hair[0] == 3),
        And(music[1] == 1, hair[1] == 3),
        And(music[2] == 1, hair[2] == 3),
        And(music[3] == 1, hair[3] == 3)
    ))

    # Clue 7: rock (music 2) is Arnold (name 1)
    solver.add(Or(
        And(music[0] == 2, name[0] == 1),
        And(music[1] == 2, name[1] == 1),
        And(music[2] == 2, name[2] == 1),
        And(music[3] == 2, name[3] == 1)
    ))

    # Clue 8: Peter (name 2) is to the right of rock music
    solver.add(Or(
        And(music[0] == 2, Or(name[1] == 2, name[2] == 2, name[3] == 2)),
        And(music[1] == 2, Or(name[2] == 2, name[3] == 2)),
        And(music[2] == 2, name[3] == 2),
        And(music[3] == 2, False)
    ))

    if solver.check() == sat:
        model = solver.model()
        name_vals = [model[name[i]].as_long() for i in range(4)]
        hair_vals = [model[hair[i]].as_long() for i in range(4)]
        music_vals = [model[music[i]].as_long() for i in range(4)]

        name_map = {0: 'Eric', 1: 'Arnold', 2: 'Peter', 3: 'Alice'}
        hair_map = {0: 'blonde', 1: 'black', 2: 'brown', 3: 'red'}
        music_map = {0: 'pop', 1: 'jazz', 2: 'rock', 3: 'classical'}

        rows = []
        for i in range(4):
            house_num = i + 1
            name_str = name_map[name_vals[i]]
            hair_str = hair_map[hair_vals[i]]
            music_str = music_map[music_vals[i]]
            rows.append([str(house_num), name_str, hair_str, music_str])

        solution = {
            "solution": {
                "header": ["House", "Name", "HairColor", "MusicGenre"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()