#!/usr/bin/env python3
import json
import itertools

def main():
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hair_colors = ["blonde", "black", "brown", "red"]
    music_genres = ["pop", "jazz", "rock", "classical"]

    for name_perm in itertools.permutations(names):
        for hair_perm in itertools.permutations(hair_colors):
            for music_perm in itertools.permutations(music_genres):
                # Clue 5: The person who loves classical music is in the first house.
                if music_perm[0] != "classical":
                    continue
                # Clue 2: The person who loves classical music is directly left of the person who has blonde hair.
                # With classical in house 1, house 2 must have blonde hair.
                if hair_perm[1] != "blonde":
                    continue
                # Clue 3: The person who has brown hair is not in the first house.
                if hair_perm[0] == "brown":
                    continue
                # Clue 4: The person who loves pop music is not in the third house.
                if music_perm[2] == "pop":
                    continue

                valid = True
                for i in range(4):
                    # Clue 1: Eric is the person who has red hair.
                    if name_perm[i] == "Eric" and hair_perm[i] != "red":
                        valid = False
                        break
                    # Clue 6: The person who loves jazz music is the person who has red hair.
                    if hair_perm[i] == "red" and music_perm[i] != "jazz":
                        valid = False
                        break
                    if music_perm[i] == "jazz" and hair_perm[i] != "red":
                        valid = False
                        break
                    # Clue 7: The person who loves rock music is Arnold.
                    if name_perm[i] == "Arnold" and music_perm[i] != "rock":
                        valid = False
                        break
                    if music_perm[i] == "rock" and name_perm[i] != "Arnold":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 8: Peter is somewhere to the right of the person who loves rock music.
                index_rock = music_perm.index("rock")
                index_peter = name_perm.index("Peter")
                if index_peter <= index_rock:
                    continue

                # Build the solution in the required format.
                rows = []
                for i in range(4):
                    rows.append([str(i+1), name_perm[i], hair_perm[i], music_perm[i]])
                result = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "MusicGenre"],
                        "rows": rows
                    }
                }
                print(json.dumps(result))
                return

if __name__ == "__main__":
    main()