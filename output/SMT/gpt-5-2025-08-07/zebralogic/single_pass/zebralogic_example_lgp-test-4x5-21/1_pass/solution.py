import json
from z3 import *

def solve_puzzle():
    # Enumerations
    Names = ["Eric", "Alice", "Peter", "Arnold"]
    Smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    Sports = ["soccer", "tennis", "basketball", "swimming"]
    Cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    Flowers = ["daffodils", "roses", "lilies", "carnations"]

    name_idx = {v: i for i, v in enumerate(Names)}
    smoothie_idx = {v: i for i, v in enumerate(Smoothies)}
    sport_idx = {v: i for i, v in enumerate(Sports)}
    car_idx = {v: i for i, v in enumerate(Cars)}
    flower_idx = {v: i for i, v in enumerate(Flowers)}

    # Variables: index 0..3 represent houses 1..4
    name = [Int(f"name_{i}") for i in range(4)]
    smoothie = [Int(f"smoothie_{i}") for i in range(4)]
    sport = [Int(f"sport_{i}") for i in range(4)]
    car = [Int(f"car_{i}") for i in range(4)]
    flower = [Int(f"flower_{i}") for i in range(4)]

    s = Solver()

    # Domains
    for i in range(4):
        s.add(And(name[i] >= 0, name[i] < 4))
        s.add(And(smoothie[i] >= 0, smoothie[i] < 4))
        s.add(And(sport[i] >= 0, sport[i] < 4))
        s.add(And(car[i] >= 0, car[i] < 4))
        s.add(And(flower[i] >= 0, flower[i] < 4))

    # All-different per attribute
    s.add(Distinct(name))
    s.add(Distinct(smoothie))
    s.add(Distinct(sport))
    s.add(Distinct(car))
    s.add(Distinct(flower))

    # Clues:

    # 1. Tesla Model 3 <-> roses
    for i in range(4):
        s.add(Implies(car[i] == car_idx["tesla model 3"], flower[i] == flower_idx["roses"]))
        s.add(Implies(flower[i] == flower_idx["roses"], car[i] == car_idx["tesla model 3"]))

    # 2. Peter is the Dragonfruit smoothie lover.
    for i in range(4):
        s.add(Implies(name[i] == name_idx["Peter"], smoothie[i] == smoothie_idx["dragonfruit"]))
        s.add(Implies(smoothie[i] == smoothie_idx["dragonfruit"], name[i] == name_idx["Peter"]))

    # 3. Desert smoothie <-> Toyota Camry
    for i in range(4):
        s.add(Implies(smoothie[i] == smoothie_idx["desert"], car[i] == car_idx["toyota camry"]))
        s.add(Implies(car[i] == car_idx["toyota camry"], smoothie[i] == smoothie_idx["desert"]))

    # 4. Tennis is in the first house (house 1 -> index 0)
    s.add(sport[0] == sport_idx["tennis"])

    # 5. Toyota Camry and basketball are next to each other.
    for i in range(4):
        neighbors = []
        if i > 0:
            neighbors.append(sport[i - 1] == sport_idx["basketball"])
        if i < 3:
            neighbors.append(sport[i + 1] == sport_idx["basketball"])
        s.add(Implies(car[i] == car_idx["toyota camry"], Or(neighbors)))

    # 6. Arnold is the person who loves basketball.
    for i in range(4):
        s.add(Implies(name[i] == name_idx["Arnold"], sport[i] == sport_idx["basketball"]))
        s.add(Implies(sport[i] == sport_idx["basketball"], name[i] == name_idx["Arnold"]))

    # 7. Honda Civic <-> daffodils
    for i in range(4):
        s.add(Implies(car[i] == car_idx["honda civic"], flower[i] == flower_idx["daffodils"]))
        s.add(Implies(flower[i] == flower_idx["daffodils"], car[i] == car_idx["honda civic"]))

    # 8. Eric is the person who loves the rose bouquet.
    for i in range(4):
        s.add(Implies(name[i] == name_idx["Eric"], flower[i] == flower_idx["roses"]))
        s.add(Implies(flower[i] == flower_idx["roses"], name[i] == name_idx["Eric"]))

    # 9. Watermelon not in the first house.
    s.add(smoothie[0] != smoothie_idx["watermelon"])

    # 10. Honda Civic is somewhere to the right of the Desert smoothie lover.
    for i in range(4):
        for j in range(4):
            s.add(Implies(And(car[i] == car_idx["honda civic"], smoothie[j] == smoothie_idx["desert"]), i > j))

    # 11. Basketball <-> lilies
    for i in range(4):
        s.add(Implies(sport[i] == sport_idx["basketball"], flower[i] == flower_idx["lilies"]))
        s.add(Implies(flower[i] == flower_idx["lilies"], sport[i] == sport_idx["basketball"]))

    # 12. Tennis and soccer are next to each other.
    for i in range(4):
        neigh_soccer = []
        if i > 0:
            neigh_soccer.append(sport[i - 1] == sport_idx["soccer"])
        if i < 3:
            neigh_soccer.append(sport[i + 1] == sport_idx["soccer"])
        s.add(Implies(sport[i] == sport_idx["tennis"], Or(neigh_soccer)))

        neigh_tennis = []
        if i > 0:
            neigh_tennis.append(sport[i - 1] == sport_idx["tennis"])
        if i < 3:
            neigh_tennis.append(sport[i + 1] == sport_idx["tennis"])
        s.add(Implies(sport[i] == sport_idx["soccer"], Or(neigh_tennis)))

    assert s.check() == sat
    m = s.model()

    # Build solution rows
    rows = []
    for i in range(4):
        rows.append([
            str(i + 1),
            Names[m[name[i]].as_long()],
            Smoothies[m[smoothie[i]].as_long()],
            Sports[m[sport[i]].as_long()],
            Cars[m[car[i]].as_long()],
            Flowers[m[flower[i]].as_long()],
        ])

    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": rows
        }
    }
    return solution

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))