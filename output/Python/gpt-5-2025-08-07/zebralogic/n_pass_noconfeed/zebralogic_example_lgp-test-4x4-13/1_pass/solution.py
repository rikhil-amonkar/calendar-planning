import json
import itertools

def solve():
    houses = (1, 2, 3, 4)

    Names = ['Alice', 'Peter', 'Arnold', 'Eric']
    Cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
    Sports = ['swimming', 'basketball', 'soccer', 'tennis']
    Drinks = ['coffee', 'water', 'milk', 'tea']

    idx_name = {n: i for i, n in enumerate(Names)}
    idx_cigar = {c: i for i, c in enumerate(Cigars)}
    idx_sport = {s: i for i, s in enumerate(Sports)}
    idx_drink = {d: i for i, d in enumerate(Drinks)}

    solution = None
    count = 0

    # Iterate over possible distributions of Sports to houses
    for sport_houses in itertools.permutations(houses):
        house_of_sport = {sport: sport_houses[idx_sport[sport]] for sport in Sports}

        # Clue 8: The person who loves basketball is in the third house.
        if house_of_sport['basketball'] != 3:
            continue

        # Iterate over Names to houses
        for name_houses in itertools.permutations(houses):
            house_of_name = {name: name_houses[idx_name[name]] for name in Names}

            # Clue 1: Peter is in the fourth house.
            if house_of_name['Peter'] != 4:
                continue

            # Clue 4: The person who loves basketball is Eric.
            if house_of_name['Eric'] != house_of_sport['basketball']:
                continue

            # Iterate cigars to houses
            for cigar_houses in itertools.permutations(houses):
                house_of_cigar = {cigar: cigar_houses[idx_cigar[cigar]] for cigar in Cigars}

                # Clue 10: Peter smokes Pall Mall.
                if house_of_cigar['pall mall'] != house_of_name['Peter']:
                    continue

                # Clue 3: Arnold smokes Blue Master.
                if house_of_cigar['blue master'] != house_of_name['Arnold']:
                    continue

                # Clue 5: Tennis lover smokes Blue Master.
                if house_of_sport['tennis'] != house_of_cigar['blue master']:
                    continue

                # Clue 9: Prince smoker loves soccer.
                if house_of_sport['soccer'] != house_of_cigar['prince']:
                    continue

                # Iterate drinks to houses
                for drink_houses in itertools.permutations(houses):
                    house_of_drink = {drink: drink_houses[idx_drink[drink]] for drink in Drinks}

                    # Clue 2: Tea drinker loves basketball.
                    if house_of_drink['tea'] != house_of_sport['basketball']:
                        continue

                    # Clue 7: Arnold drinks coffee.
                    if house_of_drink['coffee'] != house_of_name['Arnold']:
                        continue

                    # Clue 6: Two houses between water drinker and Peter.
                    if abs(house_of_drink['water'] - house_of_name['Peter']) != 3:
                        continue

                    # If all constraints satisfied, we have a solution
                    name_at = {house: name for name, house in house_of_name.items()}
                    cigar_at = {house: cigar for cigar, house in house_of_cigar.items()}
                    sport_at = {house: sport for sport, house in house_of_sport.items()}
                    drink_at = {house: drink for drink, house in house_of_drink.items()}

                    rows = []
                    for h in [1, 2, 3, 4]:
                        rows.append([str(h), name_at[h], cigar_at[h], sport_at[h], drink_at[h]])

                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                            "rows": rows
                        }
                    }
                    count += 1

    if solution is None:
        raise RuntimeError("No solution found.")
    # Optionally ensure uniqueness
    # assert count == 1, f"Expected unique solution, found {count}"

    return solution

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False))