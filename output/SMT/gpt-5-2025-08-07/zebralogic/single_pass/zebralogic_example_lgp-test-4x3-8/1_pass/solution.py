import json
from z3 import Int, Solver, Distinct, And

def solve_puzzle():
    # Houses are numbered 1..4
    houses = range(1, 5)

    # Variables represent the house number for each attribute
    # Names
    Eric = Int('Eric')
    Arnold = Int('Arnold')
    Peter = Int('Peter')
    Alice = Int('Alice')

    # Hair colors
    blonde = Int('blonde')
    black = Int('black')
    brown = Int('brown')
    red = Int('red')

    # Music genres
    pop = Int('pop')
    jazz = Int('jazz')
    rock = Int('rock')
    classical = Int('classical')

    vars_all = [Eric, Arnold, Peter, Alice, blonde, black, brown, red, pop, jazz, rock, classical]

    s = Solver()

    # Each variable must be in range 1..4
    for v in vars_all:
        s.add(And(v >= 1, v <= 4))

    # Uniqueness within each category
    s.add(Distinct(Eric, Arnold, Peter, Alice))
    s.add(Distinct(blonde, black, brown, red))
    s.add(Distinct(pop, jazz, rock, classical))

    # Clues:
    # 1. Eric is the person who has red hair.
    s.add(Eric == red)

    # 2. The person who loves classical music is directly left of the person who has blonde hair.
    # classical = i, blonde = i+1
    s.add(classical + 1 == blonde)

    # 3. The person who has brown hair is not in the first house.
    s.add(brown != 1)

    # 4. The person who loves pop music is not in the third house.
    s.add(pop != 3)

    # 5. The person who loves classical music is in the first house.
    s.add(classical == 1)

    # 6. The person who loves jazz music is the person who has red hair.
    s.add(jazz == red)

    # 7. The person who loves rock music is Arnold.
    s.add(rock == Arnold)

    # 8. Peter is somewhere to the right of the person who loves rock music.
    s.add(Peter > rock)

    if s.check() != 1:  # 1 corresponds to sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Helper to evaluate model to int
    def val(x):
        return m[x].as_long()

    # Build reverse mappings from house -> attribute name
    names_vars = {'Eric': Eric, 'Arnold': Arnold, 'Peter': Peter, 'Alice': Alice}
    hair_vars = {'blonde': blonde, 'black': black, 'brown': brown, 'red': red}
    music_vars = {'pop': pop, 'jazz': jazz, 'rock': rock, 'classical': classical}

    name_at = {val(v): k for k, v in names_vars.items()}
    hair_at = {val(v): k for k, v in hair_vars.items()}
    music_at = {val(v): k for k, v in music_vars.items()}

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": []
        }
    }

    for h in houses:
        row = [str(h), name_at[h], hair_at[h], music_at[h]]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()