import itertools
import json

def main():
    # Attributes for each category
    names = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]

    solution = None

    # Iterate over every permutation of attributes for the 4 houses.
    # The houses are indexed 0 to 3 corresponding to House 1 to House 4.
    for names_perm in itertools.permutations(names):
        for smoothies_perm in itertools.permutations(smoothies):
            # Clue 9: The Watermelon smoothie lover is not in the first house.
            if smoothies_perm[0] == "watermelon":
                continue
            for sports_perm in itertools.permutations(sports):
                # Clue 4: The person who loves tennis is in the first house.
                if sports_perm[0] != "tennis":
                    continue
                # Clue 12: The person who loves tennis and the person who loves soccer are next to each other.
                try:
                    index_tennis = sports_perm.index("tennis")
                    index_soccer = sports_perm.index("soccer")
                except ValueError:
                    continue
                if abs(index_tennis - index_soccer) != 1:
                    continue

                for cars_perm in itertools.permutations(cars):
                    # Clue 3: The Desert smoothie lover is the person who owns a Toyota Camry.
                    valid = True
                    for i in range(4):
                        if smoothies_perm[i] == "desert" and cars_perm[i] != "toyota camry":
                            valid = False
                            break
                        if cars_perm[i] == "toyota camry" and smoothies_perm[i] != "desert":
                            valid = False
                            break
                    if not valid:
                        continue

                    for flowers_perm in itertools.permutations(flowers):
                        valid_configuration = True
                        for i in range(4):
                            # Clue 2: Peter is the Dragonfruit smoothie lover.
                            if names_perm[i] == "Peter" and smoothies_perm[i] != "dragonfruit":
                                valid_configuration = False
                                break
                            
                            # Clue 1: The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
                            if cars_perm[i] == "tesla model 3" and flowers_perm[i] != "roses":
                                valid_configuration = False
                                break
                            if flowers_perm[i] == "roses" and cars_perm[i] != "tesla model 3":
                                valid_configuration = False
                                break

                            # Clue 6: Arnold is the person who loves basketball.
                            if names_perm[i] == "Arnold" and sports_perm[i] != "basketball":
                                valid_configuration = False
                                break

                            # Clue 7: The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
                            if cars_perm[i] == "honda civic" and flowers_perm[i] != "daffodils":
                                valid_configuration = False
                                break
                            if flowers_perm[i] == "daffodils" and cars_perm[i] != "honda civic":
                                valid_configuration = False
                                break

                            # Clue 8: Eric is the person who loves the rose bouquet.
                            if names_perm[i] == "Eric" and flowers_perm[i] != "roses":
                                valid_configuration = False
                                break

                            # Clue 11: The person who loves basketball is the person who loves the bouquet of lilies.
                            if sports_perm[i] == "basketball" and flowers_perm[i] != "lilies":
                                valid_configuration = False
                                break
                            if flowers_perm[i] == "lilies" and sports_perm[i] != "basketball":
                                valid_configuration = False
                                break
                        if not valid_configuration:
                            continue

                        # Clue 5: The person who owns a Toyota Camry and the person who loves basketball are next to each other.
                        try:
                            index_camry = cars_perm.index("toyota camry")
                            index_basketball = sports_perm.index("basketball")
                        except ValueError:
                            continue
                        if abs(index_camry - index_basketball) != 1:
                            continue

                        # Clue 10: The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
                        try:
                            index_desert = smoothies_perm.index("desert")
                            index_civic = cars_perm.index("honda civic")
                        except ValueError:
                            continue
                        if index_civic <= index_desert:
                            continue

                        # All constraints have been satisfied; record the solution.
                        solution = []
                        for i in range(4):
                            solution.append([
                                str(i + 1),
                                names_perm[i],
                                smoothies_perm[i],
                                sports_perm[i],
                                cars_perm[i],
                                flowers_perm[i]
                            ])
                        break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    # Build the JSON output in the exact required structure.
    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()