#!/usr/bin/env python3
import itertools
import json

def solve():
    # Define the lists for each attribute.
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]
    
    solution = None

    # Iterate over permutations for names.
    for name_perm in itertools.permutations(names):
        # Clue 8: Alice is in the third house.
        if name_perm[2] != "Alice":
            continue
        
        # Iterate over permutations for mothers.
        for mother_perm in itertools.permutations(mothers):
            # Clue 1: Alice's mother must be Kailyn.
            if mother_perm[2] != "Kailyn":
                continue
            # Clue 5: Arnold's mother must be Holly.
            try:
                index_arnold = name_perm.index("Arnold")
            except ValueError:
                continue
            if mother_perm[index_arnold] != "Holly":
                continue
            
            # Iterate over permutations for flowers.
            for flower_perm in itertools.permutations(flowers):
                # Clue 7: The bouquet of lilies is directly left of Alice.
                # Since Alice is in house3 (index 2), house2 (index 1) must have lilies.
                if flower_perm[1] != "lilies":
                    continue
                # Clue 4: Eric's flower is daffodils.
                try:
                    index_eric = name_perm.index("Eric")
                except ValueError:
                    continue
                if flower_perm[index_eric] != "daffodils":
                    continue

                # Clue 3: Peter is somewhere to the right of the person who loves carnations.
                try:
                    index_peter = name_perm.index("Peter")
                    index_carnations = flower_perm.index("carnations")
                except ValueError:
                    continue
                if not (index_peter > index_carnations):
                    continue

                # Clue 6: The person who loves carnations is somewhere to the right of the person whose mother is Holly.
                try:
                    index_holly = mother_perm.index("Holly")
                except ValueError:
                    continue
                if not (index_carnations > index_holly):
                    continue

                # Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
                try:
                    index_janelle = mother_perm.index("Janelle")
                except ValueError:
                    continue
                if not (index_janelle > index_arnold):
                    continue

                # If all constraints are satisfied, record the solution.
                houses = []
                for i in range(4):
                    houses.append({
                        "House": str(i+1),
                        "Name": name_perm[i],
                        "Mother": mother_perm[i],
                        "Flower": flower_perm[i]
                    })
                solution = houses
                break
            if solution is not None:
                break
        if solution is not None:
            break

    # Prepare the output JSON structure.
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": [[house["House"], house["Name"], house["Mother"], house["Flower"]] for house in solution]
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    solve()