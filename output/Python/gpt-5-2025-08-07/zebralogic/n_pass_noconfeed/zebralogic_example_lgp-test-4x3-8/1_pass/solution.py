import json
from itertools import permutations

def solve_puzzle():
    # Define the puzzle parameters
    houses = [1, 2, 3, 4]
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hair_colors = ["blonde", "black", "brown", "red"]
    music_genres = ["pop", "jazz", "rock", "classical"]

    solutions = []

    # Helper to get 1-based position of a value in a sequence
    def pos(seq, value):
        return seq.index(value) + 1

    # Generate permutations with basic pruning from fixed constraints
    # Constraint 5: classical music in the first house
    # Constraint 4: pop music is not in the third house
    music_candidates = []
    for mus in permutations(music_genres):
        if mus[0] != "classical":
            continue
        if mus[2] == "pop":
            continue
        music_candidates.append(mus)

    # Constraint 2 + 5 implies hair at house2 is blonde (since classical is at house1 and is directly left of blonde)
    # Constraint 3: brown hair is not in the first house
    hair_candidates = []
    for hair in permutations(hair_colors):
        if hair[1] != "blonde":
            continue
        if hair[0] == "brown":
            continue
        hair_candidates.append(hair)

    # Iterate over all combinations and apply remaining constraints
    for name_perm in permutations(names):
        for hair_perm in hair_candidates:
            for music_perm in music_candidates:
                # Constraint 1: Eric has red hair
                if pos(name_perm, "Eric") != pos(hair_perm, "red"):
                    continue

                # Constraint 6: Jazz music is the person who has red hair
                if pos(music_perm, "jazz") != pos(hair_perm, "red"):
                    continue

                # Constraint 7: Rock music is Arnold
                if pos(music_perm, "rock") != pos(name_perm, "Arnold"):
                    continue

                # Constraint 8: Peter is somewhere to the right of the person who loves rock music
                if pos(name_perm, "Peter") <= pos(music_perm, "rock"):
                    continue

                # Constraint 2 (redundant given our pruning but kept for safety):
                if pos(music_perm, "classical") + 1 != pos(hair_perm, "blonde"):
                    continue

                # All constraints satisfied; record solution
                solutions.append((name_perm, hair_perm, music_perm))

    # Expect exactly one solution for a well-posed puzzle
    if not solutions:
        raise ValueError("No solution found.")
    if len(solutions) > 1:
        # In case multiple, choose the first but this shouldn't happen for this puzzle
        pass

    name_sol, hair_sol, music_sol = solutions[0]

    # Build output JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": []
        }
    }

    for i in range(4):
        row = [str(i + 1), name_sol[i], hair_sol[i], music_sol[i]]
        output["solution"]["rows"].append(row)

    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))