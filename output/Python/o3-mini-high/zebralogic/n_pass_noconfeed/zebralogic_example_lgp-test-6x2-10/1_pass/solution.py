import itertools
import json

def solve():
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    music_genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    # Iterate over all possible permutations of names and music
    for perm_names in itertools.permutations(names):
        # Constraint 3: Carol is in the sixth house.
        if perm_names[5] != "Carol":
            continue
        # Constraint 4 and deduction: Eric must be adjacent to hip-hop (which is fixed in house 3)
        # and Constraint 2: Eric is somewhere to the left of hip-hop.
        # Given hip-hop will be fixed in house 3 (index 2), Eric must be in house 2 (index 1).
        if perm_names[1] != "Eric":
            continue
        # Constraint 6: Arnold is not in the fifth house.
        if perm_names[4] == "Arnold":
            continue

        for perm_music in itertools.permutations(music_genres):
            # Constraint 9: The person who loves hip-hop music is in the third house.
            if perm_music[2] != "hip hop":
                continue
            # Constraint 5: The person who loves country music is Carol (and Carol is in house6).
            if perm_music[5] != "country":
                continue
            # Constraint 11: The person who loves rock music is not in the fifth house.
            if perm_music[4] == "rock":
                continue

            valid = True
            pop_index = None
            # Constraint 8: The person who loves pop music is Peter.
            for i in range(6):
                if perm_music[i] == "pop":
                    if perm_names[i] != "Peter":
                        valid = False
                        break
                    pop_index = i
            if not valid or pop_index is None:
                continue

            # Constraint 1: Bob is directly left of the person who loves jazz music.
            bob_index = perm_names.index("Bob")
            if bob_index == 5 or perm_music[bob_index + 1] != "jazz":
                continue

            # Constraint 2: Eric is somewhere to the left of the person who loves hip-hop.
            # Hip-hop is in the third house (index 2) and Eric is already in house2 (index 1).
            if perm_names.index("Eric") >= 2:
                continue

            # Constraint 4: Eric and the person who loves hip-hop music are next to each other.
            if abs(perm_names.index("Eric") - 2) != 1:
                continue

            # Constraint 7: Arnold is somewhere to the right of the person who loves pop music.
            arnold_index = perm_names.index("Arnold")
            if arnold_index <= pop_index:
                continue

            # Constraint 10: There is one house between Peter and Bob.
            peter_index = perm_names.index("Peter")
            if abs(peter_index - bob_index) != 2:
                continue

            # If all constraints are satisfied, build the solution.
            solution_rows = []
            for i in range(6):
                solution_rows.append([str(i + 1), perm_names[i], perm_music[i]])
            result = {
                "solution": {
                    "header": ["House", "Name", "MusicGenre"],
                    "rows": solution_rows
                }
            }
            print(json.dumps(result))
            return

if __name__ == "__main__":
    solve()