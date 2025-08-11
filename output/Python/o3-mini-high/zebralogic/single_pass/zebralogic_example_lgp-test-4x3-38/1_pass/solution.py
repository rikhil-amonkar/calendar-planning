#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]

    # Houses are numbered 1 to 4; we use 0-indexing for the lists.
    for name_perm in itertools.permutations(names):
        # Clue 8: Alice is in the third house (index 2).
        if name_perm[2] != "Alice":
            continue

        for mother_perm in itertools.permutations(mothers):
            # Clue 1: Alice's mother's name is Kailyn.
            if mother_perm[name_perm.index("Alice")] != "Kailyn":
                continue
            # Clue 5: Arnold's mother's name is Holly.
            if mother_perm[name_perm.index("Arnold")] != "Holly":
                continue

            for flower_perm in itertools.permutations(flowers):
                # Clue 4: Eric loves a bouquet of daffodils.
                if flower_perm[name_perm.index("Eric")] != "daffodils":
                    continue

                # Clue 7: The person who loves the bouquet of lilies is directly left of Alice.
                alice_index = name_perm.index("Alice")
                if alice_index == 0 or flower_perm[alice_index - 1] != "lilies":
                    continue

                # Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
                index_janelle = mother_perm.index("Janelle")
                index_arnold = name_perm.index("Arnold")
                if index_janelle <= index_arnold:
                    continue

                # Clue 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
                index_carnations = flower_perm.index("carnations")
                index_peter = name_perm.index("Peter")
                if index_peter <= index_carnations:
                    continue

                # Clue 6: The person who loves a carnations arrangement is somewhere to the right of the person whose mother's name is Holly.
                index_holly = mother_perm.index("Holly")
                if index_carnations <= index_holly:
                    continue

                # All constraints satisfied; build the solution.
                solution = []
                for i in range(4):
                    # House numbers are 1-indexed.
                    solution.append([str(i+1), name_perm[i], mother_perm[i], flower_perm[i]])
                return solution
    return None

def main():
    solution = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "Mother's Name", "Favorite Flower"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()