import itertools
import json

def main():
    names_options = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers_options = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals_options = ["dog", "horse", "cat", "bird", "fish"]

    solution = None
    # Iterate over permutations for names, ensuring "Alice" is in house 2 and, by clue 8 and 5, "Eric" is in house 3.
    for names_perm in itertools.permutations(names_options):
        if names_perm[1] != "Alice":
            continue
        if names_perm[2] != "Eric":
            continue

        for flowers_perm in itertools.permutations(flowers_options):
            # Clue 9: The person who loves carnations is directly left of the person who loves tulips.
            pos_carnations = flowers_perm.index("carnations")
            if pos_carnations == 4 or flowers_perm[pos_carnations + 1] != "tulips":
                continue

            for animals_perm in itertools.permutations(animals_options):
                valid = True

                # Clue 10: The cat lover is not in the first house.
                if animals_perm[0] == "cat":
                    continue

                # Clue 2: The person with the lilies bouquet is the bird keeper.
                for i in range(5):
                    if flowers_perm[i] == "lilies" and animals_perm[i] != "bird":
                        valid = False
                        break
                    if animals_perm[i] == "bird" and flowers_perm[i] != "lilies":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 4: The fish enthusiast is the person who loves daffodils.
                for i in range(5):
                    if animals_perm[i] == "fish" and flowers_perm[i] != "daffodils":
                        valid = False
                        break
                    if flowers_perm[i] == "daffodils" and animals_perm[i] != "fish":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 5: The person who keeps horses is Eric.
                for i in range(5):
                    if animals_perm[i] == "horse" and names_perm[i] != "Eric":
                        valid = False
                        break
                    if names_perm[i] == "Eric" and animals_perm[i] != "horse":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 6: There are two houses between the dog owner and Bob.
                try:
                    idx_dog = animals_perm.index("dog")
                    idx_bob = names_perm.index("Bob")
                except ValueError:
                    valid = False
                if abs(idx_dog - idx_bob) != 3:
                    valid = False
                if not valid:
                    continue

                # Clue 7: The fish enthusiast is directly left of Bob.
                try:
                    idx_fish = animals_perm.index("fish")
                except ValueError:
                    valid = False
                if idx_fish == 4 or names_perm[idx_fish + 1] != "Bob":
                    valid = False
                if not valid:
                    continue

                # Clue 8: Alice is directly left of the person who keeps horses.
                try:
                    idx_alice = names_perm.index("Alice")
                except ValueError:
                    valid = False
                if idx_alice == 4 or animals_perm[idx_alice + 1] != "horse":
                    valid = False
                if not valid:
                    continue

                # Clue 3: Peter is somewhere to the right of the person who loves tulips.
                idx_peter = names_perm.index("Peter")
                idx_tulips = flowers_perm.index("tulips")
                if idx_peter <= idx_tulips:
                    valid = False
                if not valid:
                    continue

                # If all clues are satisfied, record the solution.
                solution = (names_perm, flowers_perm, animals_perm)
                break
            if solution is not None:
                break
        if solution is not None:
            break

    if solution is None:
        print("No solution found")
    else:
        names_sol, flowers_sol, animals_sol = solution
        rows = []
        for i in range(5):
            # House numbers are 1-indexed in the output.
            row = [str(i + 1), names_sol[i], flowers_sol[i], animals_sol[i]]
            rows.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()