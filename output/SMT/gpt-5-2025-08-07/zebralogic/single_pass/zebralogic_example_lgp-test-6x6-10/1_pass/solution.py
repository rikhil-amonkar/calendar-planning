import json
from z3 import Int, Solver, Distinct, And, Or, If, sat

def solve_puzzle():
    houses = list(range(1, 7))

    # Categories and values (must match prompt exactly)
    names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

    # Helper to create Z3 Int vars with safe names
    def var_name(category, value):
        safe = value.replace(" ", "_").replace("-", "_")
        return f"{category}_{safe}"

    # Create Z3 variables mapping each attribute value to a house position (1..6)
    name_vars = {v: Int(var_name("name", v)) for v in names}
    food_vars = {v: Int(var_name("food", v)) for v in foods}
    height_vars = {v: Int(var_name("height", v)) for v in heights}
    drink_vars = {v: Int(var_name("drink", v)) for v in drinks}
    pet_vars = {v: Int(var_name("pet", v)) for v in pets}
    phone_vars = {v: Int(var_name("phone", v)) for v in phones}

    s = Solver()

    # Domain constraints: each value is assigned to a house 1..6
    for d in [name_vars, food_vars, height_vars, drink_vars, pet_vars, phone_vars]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))
        # Uniqueness within each category
        s.add(Distinct(list(d.values())))

    # Clues as constraints:

    # 1. iPhone 13 is in the third house.
    s.add(phone_vars["iphone 13"] == 3)

    # 2. Bob is tall.
    s.add(name_vars["Bob"] == height_vars["tall"])

    # 3. Soup is in the second house.
    s.add(food_vars["soup"] == 2)

    # 4. Root beer directly left of Xiaomi Mi 11.
    s.add(drink_vars["root beer"] + 1 == phone_vars["xiaomi mi 11"])

    # 5. Huawei P50 is directly left of grilled cheese.
    s.add(phone_vars["huawei p50"] + 1 == food_vars["grilled cheese"])

    # 6. Stir fry person likes milk.
    s.add(food_vars["stir fry"] == drink_vars["milk"])

    # 7. Grilled cheese is tall (and Bob is tall from #2).
    s.add(food_vars["grilled cheese"] == height_vars["tall"])

    # 8. Xiaomi Mi 11 user is the coffee drinker.
    s.add(phone_vars["xiaomi mi 11"] == drink_vars["coffee"])

    # 9. OnePlus 9 user is Arnold.
    s.add(phone_vars["oneplus 9"] == name_vars["Arnold"])

    # 10. Rabbit is not in the fifth house.
    s.add(pet_vars["rabbit"] != 5)

    # 11. Hamster is somewhere to the right of Google Pixel 6.
    s.add(pet_vars["hamster"] > phone_vars["google pixel 6"])

    # 12. Super tall is the fish owner.
    s.add(height_vars["super tall"] == pet_vars["fish"])

    # 13. Fish owner is Alice.
    s.add(pet_vars["fish"] == name_vars["Alice"])

    # 14. Tea drinker is directly left of the pizza lover.
    s.add(drink_vars["tea"] + 1 == food_vars["pizza"])

    # 15. Samsung Galaxy S21 user is Carol.
    s.add(phone_vars["samsung galaxy s21"] == name_vars["Carol"])

    # 16. Pizza lover is short.
    s.add(food_vars["pizza"] == height_vars["short"])

    # 17. Arnold is very tall.
    s.add(name_vars["Arnold"] == height_vars["very tall"])

    # 18. Spaghetti eater uses a Google Pixel 6. (Interpreting "loves the spaghetti eater" as "spaghetti lover")
    s.add(food_vars["spaghetti"] == phone_vars["google pixel 6"])

    # 19. Boba tea drinker is somewhere to the right of the soup (which is in house 2).
    s.add(drink_vars["boba tea"] > food_vars["soup"])

    # 20. Hamster is not in the fifth house.
    s.add(pet_vars["hamster"] != 5)

    # 21. Very tall is not in the second house.
    s.add(height_vars["very tall"] != 2)

    # 22. Super tall is somewhere to the left of Peter.
    s.add(height_vars["super tall"] < name_vars["Peter"])

    # 23. Very short is the spaghetti eater. (Interpreting as "very short person is the spaghetti lover")
    s.add(height_vars["very short"] == food_vars["spaghetti"])

    # 24. Bird is somewhere to the left of the spaghetti eater.
    s.add(pet_vars["bird"] < food_vars["spaghetti"])

    # 25. Fish is directly left of Eric.
    s.add(pet_vars["fish"] + 1 == name_vars["Eric"])

    # 26. Dog owner likes milk.
    s.add(pet_vars["dog"] == drink_vars["milk"])

    # Solve
    if s.check() != sat:
        raise ValueError("Puzzle constraints are unsatisfiable with the given interpretation.")

    m = s.model()

    # Build reverse lookup: house -> attribute value
    def invert(category_vars):
        inv = {}
        for label, var in category_vars.items():
            inv[int(m[var].as_long())] = label
        return inv

    name_at = invert(name_vars)
    food_at = invert(food_vars)
    height_at = invert(height_vars)
    drink_at = invert(drink_vars)
    pet_at = invert(pet_vars)
    phone_at = invert(phone_vars)

    # Build the output JSON structure
    header = ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            name_at[h],
            food_at[h],
            height_at[h],
            drink_at[h],
            pet_at[h],
            phone_at[h],
        ])

    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()