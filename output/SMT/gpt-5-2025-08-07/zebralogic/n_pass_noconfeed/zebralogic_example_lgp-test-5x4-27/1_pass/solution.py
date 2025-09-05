import json
from z3 import Solver, Int, Distinct, And, Or, Abs, sat

def main():
    houses = [1, 2, 3, 4, 5]

    names = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
    birthdays = ["april", "feb", "mar", "jan", "sept"]
    cigars = ["pall mall", "prince", "dunhill", "blends", "blue master"]
    drinks = ["water", "coffee", "tea", "milk", "root beer"]

    # Create position variables for each attribute value (mapping each value to a house 1..5)
    def create_pos_vars(values, prefix):
        return {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in values}

    name_pos = create_pos_vars(names, "name")
    bday_pos = create_pos_vars(birthdays, "bday")
    cigar_pos = create_pos_vars(cigars, "cigar")
    drink_pos = create_pos_vars(drinks, "drink")

    s = Solver()

    # Each variable is within house range 1..5
    for d in [name_pos, bday_pos, cigar_pos, drink_pos]:
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # Uniqueness within each category
    s.add(Distinct([name_pos[n] for n in names]))
    s.add(Distinct([bday_pos[b] for b in birthdays]))
    s.add(Distinct([cigar_pos[c] for c in cigars]))
    s.add(Distinct([drink_pos[d] for d in drinks]))

    # Clues:
    # 1. The root beer lover is Eric.
    s.add(drink_pos["root beer"] == name_pos["Eric"])

    # 2. The person partial to Pall Mall is in the third house.
    s.add(cigar_pos["pall mall"] == 3)

    # 3. The person whose birthday is in April is Bob.
    s.add(bday_pos["april"] == name_pos["Bob"])

    # 4. The Dunhill smoker is the person whose birthday is in March.
    s.add(cigar_pos["dunhill"] == bday_pos["mar"])

    # 5. Peter is somewhere to the right of the root beer lover.
    s.add(name_pos["Peter"] > drink_pos["root beer"])

    # 6. There is one house between the person whose birthday is in January and Peter.
    s.add(Abs(bday_pos["jan"] - name_pos["Peter"]) == 2)

    # 7. The person who smokes many unique blends is the person whose birthday is in February.
    s.add(cigar_pos["blends"] == bday_pos["feb"])

    # 8. The person whose birthday is in February is in the second house.
    s.add(bday_pos["feb"] == 2)

    # 9. Arnold is directly left of Peter.
    s.add(name_pos["Arnold"] + 1 == name_pos["Peter"])

    # 10. The person who likes milk is not in the fifth house.
    s.add(drink_pos["milk"] != 5)

    # 11. The person who smokes Blue Master is the coffee drinker.
    s.add(cigar_pos["blue master"] == drink_pos["coffee"])

    # 12. There is one house between the tea drinker and the coffee drinker.
    s.add(Abs(drink_pos["tea"] - drink_pos["coffee"]) == 2)

    # 13. Eric is in the third house.
    s.add(name_pos["Eric"] == 3)

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable or unknown")

    m = s.model()

    # Invert mapping: for each house, find the attribute value at that house
    def invert(model, pos_dict, values):
        arr = [""] * 5
        for v in values:
            h = model.eval(pos_dict[v]).as_long()
            arr[h - 1] = v
        return arr

    names_by_house = invert(m, name_pos, names)
    bdays_by_house = invert(m, bday_pos, birthdays)
    cigars_by_house = invert(m, cigar_pos, cigars)
    drinks_by_house = invert(m, drink_pos, drinks)

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": []
        }
    }

    for i in range(5):
        row = [
            str(i + 1),
            names_by_house[i],
            bdays_by_house[i],
            cigars_by_house[i],
            drinks_by_house[i]
        ]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()