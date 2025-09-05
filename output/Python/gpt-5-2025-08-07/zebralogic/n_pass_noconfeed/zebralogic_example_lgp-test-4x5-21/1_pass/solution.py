import json
from itertools import permutations

def solve_puzzle():
    houses = [0, 1, 2, 3]  # 0-based indices for houses 1..4

    names = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]

    solution_rows = None

    for name_perm in permutations(names):
        pos_name = {name: idx for idx, name in enumerate(name_perm)}

        for sport_perm in permutations(sports):
            # Clue 4: Tennis is in the first house (index 0)
            if sport_perm[0] != "tennis":
                continue
            # Clue 12: Tennis and Soccer are next to each other -> with Tennis at 1, Soccer must be at 2 (index 1)
            if sport_perm[1] != "soccer":
                continue
            # Clue 6: Arnold loves basketball
            if sport_perm[pos_name["Arnold"]] != "basketball":
                continue

            for car_perm in permutations(cars):
                # Clues 1 & 8: Tesla Model 3 owner loves roses; Eric loves roses -> Eric owns Tesla
                if car_perm[pos_name["Eric"]] != "tesla model 3":
                    continue
                # Clue 5: Camry and Basketball are next to each other
                if abs(car_perm.index("toyota camry") - sport_perm.index("basketball")) != 1:
                    continue

                for smoothie_perm in permutations(smoothies):
                    # Clue 9: Watermelon not in the first house
                    if smoothie_perm[0] == "watermelon":
                        continue
                    # Clue 2: Peter is the Dragonfruit smoothie lover
                    if smoothie_perm[pos_name["Peter"]] != "dragonfruit":
                        continue
                    # Clue 3: Desert smoothie lover owns a Toyota Camry
                    if smoothie_perm.index("desert") != car_perm.index("toyota camry"):
                        continue
                    # Clue 10: Honda Civic is to the right of the Desert smoothie lover
                    if car_perm.index("honda civic") <= smoothie_perm.index("desert"):
                        continue

                    for flower_perm in permutations(flowers):
                        # Clue 7: Honda Civic owner loves daffodils
                        if car_perm.index("honda civic") != flower_perm.index("daffodils"):
                            continue
                        # Clue 11: Basketball lover loves lilies
                        if sport_perm.index("basketball") != flower_perm.index("lilies"):
                            continue
                        # Clues 1 & 8: Tesla <-> Roses and Eric loves Roses
                        if car_perm.index("tesla model 3") != flower_perm.index("roses"):
                            continue
                        if flower_perm[pos_name["Eric"]] != "roses":
                            continue

                        # Build solution rows (convert to 1-based house numbers as strings)
                        solution_rows = []
                        for i in range(4):
                            row = [
                                str(i + 1),
                                name_perm[i],
                                smoothie_perm[i],
                                sport_perm[i],
                                car_perm[i],
                                flower_perm[i],
                            ]
                            solution_rows.append(row)
                        return solution_rows

    return solution_rows

def main():
    rows = solve_puzzle()
    if rows is None:
        raise RuntimeError("No solution found for the given puzzle.")

    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": rows
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()