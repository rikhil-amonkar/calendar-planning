#!/usr/bin/env python3
import json
import itertools

def main():
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    solution = None

    # Iterate over all possible permutations of names and genres.
    # Houses are indexed 0 to 5 corresponding to house numbers 1 to 6.
    for name_perm in itertools.permutations(names):
        # Constraint 3: Carol is in the sixth house.
        if name_perm[5] != "Carol":
            continue
        # Constraint from clues 2 and 4 (combined): Eric must be immediately to the left of the hip-hop house.
        # Since the hip-hop house is fixed to house 3 (index 2 by clue 9), Eric must be in house 2 (index 1).
        if name_perm[1] != "Eric":
            continue
        # Constraint 6: Arnold is not in the fifth house.
        if name_perm[4] == "Arnold":
            continue

        for genre_perm in itertools.permutations(genres):
            # Constraint 9: The person who loves hip-hop music is in the third house.
            if genre_perm[2] != "hip hop":
                continue
            # Constraint 5: The person who loves country music is Carol.
            # Since Carol must be in house 6 (index 5), country must be in house 6.
            if genre_perm[5] != "country":
                continue
            # Constraint 11: The person who loves rock music is not in the fifth house.
            if genre_perm[4] == "rock":
                continue

            # Constraint 1: Bob is directly left of the person who loves jazz music.
            pos_bob = name_perm.index("Bob")
            # Bob cannot be in the last house because he must have a house to his right.
            if pos_bob == 5 or genre_perm[pos_bob + 1] != "jazz":
                continue

            # Constraint 8: The person who loves pop music is Peter.
            # This enforces that the house with pop must have Peter.
            try:
                pos_pop = genre_perm.index("pop")
            except ValueError:
                continue
            if name_perm[pos_pop] != "Peter":
                continue
            # Also, if Peter's house doesn't have pop, the constraint fails.
            pos_peter = name_perm.index("Peter")
            if genre_perm[pos_peter] != "pop":
                continue

            # Constraint 7: Arnold is somewhere to the right of the person who loves pop music.
            pos_arnold = name_perm.index("Arnold")
            if pos_arnold <= pos_pop:
                continue

            # Constraint 10: There is one house between Peter and Bob.
            if abs(pos_peter - pos_bob) != 2:
                continue

            # Constraint 2 and 4: Eric is somewhere to the left of the person who loves hip-hop music
            # and Eric and the hip-hop lover are next to each other.
            # Since hip-hop is in house 3 (index 2) and we already forced Eric to be in house 2 (index 1),
            # these conditions are automatically satisfied.
            
            # All constraints satisfied: record the solution.
            solution = (name_perm, genre_perm)
            break
        if solution is not None:
            break

    if solution is None:
        result = {"solution": {"header": ["House", "Name", "MusicGenre"], "rows": []}}
    else:
        solved_names, solved_genres = solution
        rows = []
        for i in range(6):
            # House numbers are 1-indexed as strings.
            rows.append([str(i+1), solved_names[i], solved_genres[i]])
        result = {
            "solution": {
                "header": ["House", "Name", "MusicGenre"],
                "rows": rows
            }
        }

    print(json.dumps(result))

if __name__ == "__main__":
    main()