import json
from z3 import Solver, Int, Distinct, Or, And

def sanitize(s):
    return s.lower().replace(' ', '_').replace('-', '').replace('/', '').replace('.', '')

def make_vars(prefix, items):
    return {item: Int(f"{prefix}_{sanitize(item)}") for item in items}

def exactly_between(x, y, k):
    # |x - y| == k
    return Or(x == y + k, y == x + k)

def adjacent(x, y):
    return exactly_between(x, y, 1)

def main():
    houses = list(range(1, 7))

    Names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
    Birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
    Foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    Heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
    Cars = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

    # Create Z3 variables for positions (house indices 1..6) of each attribute value
    posName = make_vars("name", Names)
    posBday = make_vars("bday", Birthdays)
    posFood = make_vars("food", Foods)
    posHeight = make_vars("height", Heights)
    posCar = make_vars("car", Cars)

    s = Solver()

    # Domain and distinctness constraints
    for d in [posName, posBday, posFood, posHeight, posCar]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))
        s.add(Distinct(list(d.values())))

    # Clues encoding
    # 1. Honda Civic owner is short.
    s.add(posCar["honda civic"] == posHeight["short"])

    # 2. Ford F-150 is in the fifth house.
    s.add(posCar["ford f150"] == 5)

    # 3. Stir fry is left of Eric.
    s.add(posFood["stir fry"] < posName["Eric"])

    # 4. May is left of Carol.
    s.add(posBday["may"] < posName["Carol"])

    # 5. Very short is left of April.
    s.add(posHeight["very short"] < posBday["april"])

    # 6. BMW 3 Series is not in the third house.
    s.add(posCar["bmw 3 series"] != 3)

    # 7. Two houses between stir fry and pizza.
    s.add(exactly_between(posFood["stir fry"], posFood["pizza"], 3))

    # 8. Soup is directly left of Eric.
    s.add(posFood["soup"] + 1 == posName["Eric"])

    # 9. Spaghetti eater and May are next to each other.
    s.add(adjacent(posFood["spaghetti"], posBday["may"]))

    # 10. Alice is directly left of BMW 3 Series owner.
    s.add(posName["Alice"] + 1 == posCar["bmw 3 series"])

    # 11. Tesla Model 3 is left of tall.
    s.add(posCar["tesla model 3"] < posHeight["tall"])

    # 12. Very tall owns a Toyota Camry.
    s.add(posHeight["very tall"] == posCar["toyota camry"])

    # 13. Peter is directly left of pizza lover.
    s.add(posName["Peter"] + 1 == posFood["pizza"])

    # 14. Stew is not in the third house.
    s.add(posFood["stew"] != 3)

    # 15. One house between September and very short.
    s.add(exactly_between(posBday["sept"], posHeight["very short"], 2))

    # 16. One house between March and super tall.
    s.add(exactly_between(posBday["mar"], posHeight["super tall"], 2))

    # 17. Tall is Bob.
    s.add(posHeight["tall"] == posName["Bob"])

    # 18. May is to the right of Alice.
    s.add(posBday["may"] > posName["Alice"])

    # 19. Very short is in the fourth house.
    s.add(posHeight["very short"] == 4)

    # 20. March birthday is short.
    s.add(posBday["mar"] == posHeight["short"])

    # 21. Carol owns a Tesla Model 3.
    s.add(posName["Carol"] == posCar["tesla model 3"])

    # 22. Eric has January birthday.
    s.add(posName["Eric"] == posBday["jan"])

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Build solution rows per house
    def invert(mapping):
        # returns dict house_index -> attribute_value
        return {m[var].as_long(): key for key, var in mapping.items()}

    invName = invert(posName)
    invBday = invert(posBday)
    invFood = invert(posFood)
    invHeight = invert(posHeight)
    invCar = invert(posCar)

    rows = []
    for h in houses:
        rows.append([
            str(h),
            invName[h],
            invBday[h],
            invFood[h],
            invHeight[h],
            invCar[h],
        ])

    out = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": rows
        }
    }

    print(json.dumps(out, ensure_ascii=False))

if __name__ == "__main__":
    main()