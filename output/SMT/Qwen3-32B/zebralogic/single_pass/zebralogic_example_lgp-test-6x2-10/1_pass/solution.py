import json
from z3 import *

def solve_puzzle():
    solver = Solver()

    names = [Int(f'name_{i}') for i in range(6)]
    musics = [Int(f'music_{i}') for i in range(6)]

    solver.add(Distinct(names))
    solver.add(Distinct(musics))

    # Clue 3: Carol in house 6
    solver.add(names[5] == 4)
    # Clue 5: Carol's music is country
    solver.add(musics[5] == 5)
    # Clue 9: house 3 has hip hop
    solver.add(musics[2] == 4)
    # Clue 8: Peter's music is pop
    for i in range(6):
        solver.add(Implies(names[i] == 2, musics[i] == 1))
    # Clue 10: Peter and Bob are two apart
    for i in range(6):
        for j in range(6):
            if abs(i - j) != 2:
                solver.add(Not(And(names[i] == 2, names[j] == 5)))
    # Clue 7: Arnold is to the right of Peter
    for a in range(6):
        for p in range(6):
            solver.add(Implies(And(names[a] == 0, names[p] == 2), a > p))
    # Clue 6: Arnold not in house 5
    solver.add(names[4] != 0)
    # Clue 1: Bob directly left of jazz
    for i in range(5):
        solver.add(Implies(names[i] == 5, musics[i+1] == 0))
    # Clue 11: Rock not in house 5
    solver.add(musics[4] != 3)
    # Clue 2 and 4: Eric in house 2
    solver.add(names[1] == 1)

    if solver.check() == sat:
        model = solver.model()
        names_list = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
        music_list = ["jazz", "pop", "classical", "rock", "hip hop", "country"]
        rows = []
        for i in range(6):
            house_num = i + 1
            name_idx = model.eval(names[i]).as_long()
            music_idx = model.eval(musics[i]).as_long()
            rows.append([str(house_num), names_list[name_idx], music_list[music_idx]])
        return {
            "solution": {
                "header": ["House", "Name", "MusicGenre"],
                "rows": rows
            }
        }
    else:
        return "No solution found."

result = solve_puzzle()
print(json.dumps(result, indent=2))