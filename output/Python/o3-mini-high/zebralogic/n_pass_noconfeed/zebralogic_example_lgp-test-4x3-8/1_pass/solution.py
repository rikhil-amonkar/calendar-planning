import itertools
import json

def solve_puzzle():
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hair_colors = ["blonde", "black", "brown", "red"]
    music_genres = ["pop", "jazz", "rock", "classical"]

    solution_found = None

    # Iterate over all possible assignments for names, hair colors, and music genres
    for name_perm in itertools.permutations(names):
        for hair_perm in itertools.permutations(hair_colors):
            # Clue 3: The person who has brown hair is not in the first house.
            if hair_perm[0] == "brown":
                continue
            # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
            # Clue 5: The person who loves classical music is in the first house.
            # Therefore, house 1 must be classical and house 2 must have blonde hair.
            if hair_perm[1] != "blonde":
                continue
            for music_perm in itertools.permutations(music_genres):
                # Clue 5: The person who loves classical music is in the first house.
                if music_perm[0] != "classical":
                    continue
                # Clue 4: The person who loves pop music is not in the third house.
                if music_perm[2] == "pop":
                    continue

                # Clue 1 & 6: Eric is the person who has red hair and the person with red hair loves jazz.
                index_eric = name_perm.index("Eric")
                if hair_perm[index_eric] != "red" or music_perm[index_eric] != "jazz":
                    continue

                # Clue 7: The person who loves rock music is Arnold.
                index_arnold = name_perm.index("Arnold")
                if music_perm[index_arnold] != "rock":
                    continue

                # Clue 8: Peter is somewhere to the right of the person who loves rock music (Arnold).
                index_peter = name_perm.index("Peter")
                if index_peter <= index_arnold:
                    continue

                # Clue 2 (generalized check):
                # The house with classical music should be immediately to the left of the house with blonde hair.
                # Due to fixed positions, if classical music is at house 1 then house 2 must have blonde hair.
                if 0 < 3:  # always true; we already required hair_perm[1]=="blonde"
                    pass

                # If all constraints are satisfied, construct the solution.
                solution_found = []
                for i in range(4):
                    solution_found.append([str(i + 1), name_perm[i], hair_perm[i], music_perm[i]])
                return solution_found
    return None

def main():
    solution = solve_puzzle()
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()