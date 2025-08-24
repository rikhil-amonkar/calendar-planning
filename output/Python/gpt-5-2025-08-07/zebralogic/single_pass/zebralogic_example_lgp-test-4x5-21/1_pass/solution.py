import json
from itertools import permutations

def solve():
    houses = list(range(4))  # indices 0..3 correspond to houses 1..4

    Names = ['Eric', 'Alice', 'Peter', 'Arnold']
    Smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    Sports = ['soccer', 'tennis', 'basketball', 'swimming']
    Cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
    Flowers = ['daffodils', 'roses', 'lilies', 'carnations']

    solutions = []

    for names in permutations(Names):
        # Constraint 6: Arnold loves basketball -> cannot be in house 1 (tennis)
        if names[0] == 'Arnold':
            continue

        idx_by_name = {name: i for i, name in enumerate(names)}

        # Sports with constraints: house1=tennis, house2=soccer
        for sports in permutations(Sports):
            if sports[0] != 'tennis':
                continue  # Clue 4
            if sports[1] != 'soccer':
                continue  # From Clue 12 and 4, ensures adjacency too

            # Clue 6: Arnold is the person who loves basketball
            if sports[idx_by_name['Arnold']] != 'basketball':
                continue

            # Smoothies with constraints
            for smoothies in permutations(Smoothies):
                # Clue 2: Peter is the Dragonfruit smoothie lover
                if smoothies[idx_by_name['Peter']] != 'dragonfruit':
                    continue
                # Clue 9: Watermelon smoothie lover is not in the first house
                if smoothies[0] == 'watermelon':
                    continue

                # Cars with constraints
                for cars in permutations(Cars):
                    # From Clues 1 and 8: Tesla Model 3 owner loves roses and Eric loves roses -> Eric owns Tesla
                    if cars[idx_by_name['Eric']] != 'tesla model 3':
                        continue

                    # Clue 3: Desert smoothie lover owns Toyota Camry (bidirectional)
                    consistent = True
                    for i in houses:
                        if (smoothies[i] == 'desert') != (cars[i] == 'toyota camry'):
                            consistent = False
                            break
                    if not consistent:
                        continue

                    # Clue 5: Toyota Camry and basketball are next to each other
                    idx_camry = cars.index('toyota camry')
                    idx_basket = sports.index('basketball')
                    if abs(idx_camry - idx_basket) != 1:
                        continue

                    # Clue 10: Honda Civic is to the right of the Desert/Camry
                    idx_honda = cars.index('honda civic')
                    if not (idx_honda > idx_camry):
                        continue

                    # Flowers with constraints
                    for flowers in permutations(Flowers):
                        # Clue 8: Eric loves roses
                        if flowers[idx_by_name['Eric']] != 'roses':
                            continue
                        # Clue 1: Tesla owner loves roses
                        if flowers[cars.index('tesla model 3')] != 'roses':
                            continue
                        # Clue 7: Honda Civic <-> daffodils
                        if flowers[cars.index('honda civic')] != 'daffodils':
                            continue
                        # Clue 11: Basketball <-> lilies
                        if flowers[sports.index('basketball')] != 'lilies':
                            continue

                        # All constraints satisfied, record solution
                        solutions.append({
                            "names": names,
                            "smoothies": smoothies,
                            "sports": sports,
                            "cars": cars,
                            "flowers": flowers
                        })

    # Prepare output (assume unique solution)
    if not solutions:
        raise RuntimeError("No solution found")
    sol = solutions[0]

    header = ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"]
    rows = []
    for i in range(4):
        rows.append([
            str(i + 1),
            sol["names"][i],
            sol["smoothies"][i],
            sol["sports"][i],
            sol["cars"][i],
            sol["flowers"][i]
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    solve()