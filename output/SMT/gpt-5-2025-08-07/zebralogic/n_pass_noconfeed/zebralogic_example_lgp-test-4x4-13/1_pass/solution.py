import json
from z3 import Int, Solver, Distinct, And, Or

def solve_puzzle():
    houses = [1, 2, 3, 4]

    # Categories and values
    Names = ["Alice", "Peter", "Arnold", "Eric"]
    Cigars = ["prince", "dunhill", "blue master", "pall mall"]
    Sports = ["swimming", "basketball", "soccer", "tennis"]
    Drinks = ["coffee", "water", "milk", "tea"]

    # Create Z3 variables: each value maps to a house number 1..4
    name_vars = {n: Int(n) for n in Names}
    cigar_vars = {c: Int(c.replace(" ", "_")) for c in Cigars}
    sport_vars = {s: Int(s.replace(" ", "_")) for s in Sports}
    drink_vars = {d: Int(d.replace(" ", "_")) for d in Drinks}

    s = Solver()

    # Domain constraints: all variables are in 1..4
    for var in list(name_vars.values()) + list(cigar_vars.values()) + list(sport_vars.values()) + list(drink_vars.values()):
        s.add(And(var >= 1, var <= 4))

    # Uniqueness within each category
    s.add(Distinct([name_vars[n] for n in Names]))
    s.add(Distinct([cigar_vars[c] for c in Cigars]))
    s.add(Distinct([sport_vars[x] for x in Sports]))
    s.add(Distinct([drink_vars[d] for d in Drinks]))

    # Helper to refer to variables
    Peter = name_vars["Peter"]
    Arnold = name_vars["Arnold"]
    Eric = name_vars["Eric"]
    Alice = name_vars["Alice"]

    prince = cigar_vars["prince"]
    dunhill = cigar_vars["dunhill"]
    blue_master = cigar_vars["blue master"]
    pall_mall = cigar_vars["pall mall"]

    swimming = sport_vars["swimming"]
    basketball = sport_vars["basketball"]
    soccer = sport_vars["soccer"]
    tennis = sport_vars["tennis"]

    coffee = drink_vars["coffee"]
    water = drink_vars["water"]
    milk = drink_vars["milk"]
    tea = drink_vars["tea"]

    # Clues as constraints
    # 1. Peter is in the fourth house.
    s.add(Peter == 4)

    # 2. The tea drinker is the person who loves basketball.
    s.add(tea == basketball)

    # 3. Arnold is the person who smokes Blue Master.
    s.add(Arnold == blue_master)

    # 4. The person who loves basketball is Eric.
    s.add(basketball == Eric)

    # 5. The person who loves tennis is the person who smokes Blue Master.
    s.add(tennis == blue_master)

    # 6. There are two houses between the one who only drinks water and Peter.
    s.add(Or(water == Peter + 3, water == Peter - 3))

    # 7. The coffee drinker is Arnold.
    s.add(coffee == Arnold)

    # 8. The person who loves basketball is in the third house.
    s.add(basketball == 3)

    # 9. The Prince smoker is the person who loves soccer.
    s.add(prince == soccer)

    # 10. Peter is the person partial to Pall Mall.
    s.add(Peter == pall_mall)

    if s.check() != 1:  # z3.sat == 1
        raise RuntimeError("No solution found")

    m = s.model()

    # Build house -> attribute mappings
    house_to_name = {}
    for n, v in name_vars.items():
        house_to_name[m.eval(v).as_long()] = n

    house_to_cigar = {}
    for c, v in cigar_vars.items():
        house_to_cigar[m.eval(v).as_long()] = c

    house_to_sport = {}
    for sp, v in sport_vars.items():
        house_to_sport[m.eval(v).as_long()] = sp

    house_to_drink = {}
    for d, v in drink_vars.items():
        house_to_drink[m.eval(v).as_long()] = d

    # Prepare JSON output
    header = ["House", "Name", "Cigar", "FavoriteSport", "Drink"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            house_to_name[h],
            house_to_cigar[h],
            house_to_sport[h],
            house_to_drink[h],
        ])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    res = solve_puzzle()
    print(json.dumps(res, ensure_ascii=False))