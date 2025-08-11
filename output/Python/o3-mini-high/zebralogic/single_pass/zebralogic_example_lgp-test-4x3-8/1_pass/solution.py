#!/usr/bin/env python3
import itertools
import json

def solve():
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hairs = ["blonde", "black", "brown", "red"]
    musics = ["pop", "jazz", "rock", "classical"]

    # There are 4 houses indexed 0-3 (House 1 to House 4)
    for perm_names in itertools.permutations(names):
        for perm_hairs in itertools.permutations(hairs):
            for perm_musics in itertools.permutations(musics):
                # Clue 5: The person who loves classical music is in the first house.
                if perm_musics[0] != "classical":
                    continue
                # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
                # Since classical is in house 1 (index 0), the house to its right (index 1) must have blonde hair.
                if perm_hairs[1] != "blonde":
                    continue
                # Clue 3: The person who has brown hair is not in the first house.
                if perm_hairs[0] == "brown":
                    continue
                # Clue 4: The person who loves pop music is not in the third house.
                if perm_musics[2] == "pop":
                    continue

                valid = True
                # Clue 1: Eric is the person who has red hair.
                for i in range(4):
                    if perm_names[i] == "Eric" and perm_hairs[i] != "red":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 6: The person who loves jazz music is the person who has red hair.
                for i in range(4):
                    if perm_musics[i] == "jazz" and perm_hairs[i] != "red":
                        valid = False
                        break
                    if perm_hairs[i] == "red" and perm_musics[i] != "jazz":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 7: The person who loves rock music is Arnold.
                for i in range(4):
                    if perm_names[i] == "Arnold" and perm_musics[i] != "rock":
                        valid = False
                        break
                    if perm_musics[i] == "rock" and perm_names[i] != "Arnold":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 8: Peter is somewhere to the right of the person who loves rock music.
                rock_index = perm_musics.index("rock")
                peter_index = perm_names.index("Peter")
                if peter_index <= rock_index:
                    continue

                # If all constraints are satisfied, format the solution.
                solution_rows = []
                for i in range(4):
                    # Houses are numbered 1 to 4.
                    solution_rows.append([str(i + 1), perm_names[i], perm_hairs[i], perm_musics[i]])

                return {
                    "solution": {
                        "header": ["House", "Name", "hair color", "favorite music genre"],
                        "rows": solution_rows
                    }
                }
    return None

def main():
    sol = solve()
    print(json.dumps(sol))

if __name__ == "__main__":
    main()