import json
from z3 import *

def solve():
    # Enumerations
    NAMES = ["Alice", "Peter", "Arnold", "Eric"]
    CIGARS = ["prince", "dunhill", "blue master", "pall mall"]
    SPORTS = ["swimming", "basketball", "soccer", "tennis"]
    DRINKS = ["coffee", "water", "milk", "tea"]

    # Indices for convenience
    Alice, Peter, Arnold, Eric = range(4)
    prince, dunhill, blue_master, pall_mall = range(4)
    swimming, basketball, soccer, tennis = range(4)
    coffee, water, milk, tea = range(4)

    # Variables: for each house (0..3), assign the index of the attribute
    Name = [Int(f"Name_{i}") for i in range(4)]
    Cigar = [Int(f"Cigar_{i}") for i in range(4)]
    Sport = [Int(f"Sport_{i}") for i in range(4)]
    Drink = [Int(f"Drink_{i}") for i in range(4)]

    s = Solver()

    # Domains
    for arr in [Name, Cigar, Sport, Drink]:
        for v in arr:
            s.add(v >= 0, v < 4)
        s.add(Distinct(arr))

    # Helper: positions of certain attributes
    posPeter = Int("posPeter")
    posWater = Int("posWater")
    s.add(And(posPeter >= 0, posPeter < 4, posWater >= 0, posWater < 4))
    s.add(Or(*[And(posPeter == i, Name[i] == Peter) for i in range(4)]))
    s.add(Or(*[And(posWater == i, Drink[i] == water) for i in range(4)]))

    # Clues:
    # 1. Peter is in the fourth house.
    s.add(Name[3] == Peter)

    # 2. The tea drinker is the person who loves basketball.
    for i in range(4):
        s.add((Drink[i] == tea) == (Sport[i] == basketball))

    # 3. Arnold is the person who smokes Blue Master.
    for i in range(4):
        s.add((Name[i] == Arnold) == (Cigar[i] == blue_master))

    # 4. The person who loves basketball is Eric.
    for i in range(4):
        s.add((Sport[i] == basketball) == (Name[i] == Eric))

    # 5. The person who loves tennis is the person who smokes Blue Master.
    for i in range(4):
        s.add((Sport[i] == tennis) == (Cigar[i] == blue_master))

    # 6. There are two houses between the one who only drinks water and Peter.
    s.add(Or(posWater == posPeter + 3, posWater == posPeter - 3))

    # 7. The coffee drinker is Arnold.
    for i in range(4):
        s.add((Drink[i] == coffee) == (Name[i] == Arnold))

    # 8. The person who loves basketball is in the third house.
    s.add(Sport[2] == basketball)

    # 9. The Prince smoker is the person who loves soccer.
    for i in range(4):
        s.add((Cigar[i] == prince) == (Sport[i] == soccer))

    # 10. Peter is the person partial to Pall Mall.
    for i in range(4):
        s.add((Name[i] == Peter) == (Cigar[i] == pall_mall))

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    rows = []
    for i in range(4):
        name_str = NAMES[m.evaluate(Name[i]).as_long()]
        cigar_str = CIGARS[m.evaluate(Cigar[i]).as_long()]
        sport_str = SPORTS[m.evaluate(Sport[i]).as_long()]
        drink_str = DRINKS[m.evaluate(Drink[i]).as_long()]
        rows.append([str(i + 1), name_str, cigar_str, sport_str, drink_str])

    result = {
        "solution": {
            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve()