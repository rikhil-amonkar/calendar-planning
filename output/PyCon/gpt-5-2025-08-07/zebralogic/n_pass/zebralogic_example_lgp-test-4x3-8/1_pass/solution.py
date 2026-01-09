import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4]

    names = ["Eric", "Arnold", "Peter", "Alice"]
    hairs = ["blonde", "black", "brown", "red"]
    musics = ["pop", "jazz", "rock", "classical"]

    problem = Problem()

    # Add variables with domains for each category
    for n in names:
        problem.addVariable(n, houses)
    for h in hairs:
        problem.addVariable(h, houses)
    for m in musics:
        problem.addVariable(m, houses)

    # Each category must be a permutation (all different within category)
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), hairs)
    problem.addConstraint(AllDifferentConstraint(), musics)

    # Clue 1: Eric is the person who has red hair.
    problem.addConstraint(lambda eric, red: eric == red, ("Eric", "red"))

    # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
    problem.addConstraint(lambda classical, blonde: classical == blonde - 1, ("classical", "blonde"))

    # Clue 3: The person who has brown hair is not in the first house.
    problem.addConstraint(lambda brown: brown != 1, ("brown",))

    # Clue 4: The person who loves pop music is not in the third house.
    problem.addConstraint(lambda pop: pop != 3, ("pop",))

    # Clue 5: The person who loves classical music is in the first house.
    problem.addConstraint(lambda classical: classical == 1, ("classical",))

    # Clue 6: The person who loves jazz music is the person who has red hair.
    problem.addConstraint(lambda jazz, red: jazz == red, ("jazz", "red"))

    # Clue 7: The person who loves rock music is Arnold.
    problem.addConstraint(lambda rock, arnold: rock == arnold, ("rock", "Arnold"))

    # Clue 8: Peter is somewhere to the right of the person who loves rock music.
    problem.addConstraint(lambda peter, rock: peter > rock, ("Peter", "rock"))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Assume unique solution for this puzzle; take the first
    sol = solutions[0]

    # Build mapping from house -> attributes
    house_to_name = {sol[name]: name for name in names}
    house_to_hair = {sol[hair]: hair for hair in hairs}
    house_to_music = {sol[music]: music for music in musics}

    rows = []
    for h in houses:
        row = [str(h), house_to_name[h], house_to_hair[h], house_to_music[h]]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()