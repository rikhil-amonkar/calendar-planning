import json
from z3 import *

def main():
    # Define categories and their values
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    foods = ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"]
    cars = ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"]
    phones = ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"]
    occupations = ["teacher", "lawyer", "doctor", "artist", "engineer"]
    drinks = ["tea", "milk", "water", "root beer", "coffee"]

    s = Solver()

    # Create position variables for each value (position is 1..5)
    def mk_vars(values, prefix):
        d = {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in values}
        for v in values:
            s.add(d[v] >= 1, d[v] <= 5)
        s.add(Distinct([d[v] for v in values]))
        return d

    name_pos = mk_vars(names, "Name")
    food_pos = mk_vars(foods, "Food")
    car_pos = mk_vars(cars, "Car")
    phone_pos = mk_vars(phones, "Phone")
    occ_pos = mk_vars(occupations, "Occ")
    drink_pos = mk_vars(drinks, "Drink")

    # Helper constraints
    def direct_left(a, b):
        s.add(a + 1 == b)

    def next_to(a, b):
        s.add(Or(a + 1 == b, b + 1 == a))

    def left_of(a, b):
        s.add(a < b)

    # Clues:
    # 1. The root beer lover is the person who owns a Honda Civic.
    s.add(drink_pos["root beer"] == car_pos["honda civic"])

    # 2. The person who likes milk is directly left of the person who loves eating grilled cheese.
    direct_left(drink_pos["milk"], food_pos["grilled cheese"])

    # 3. Alice is the person who uses a Samsung Galaxy S21.
    s.add(name_pos["Alice"] == phone_pos["samsung galaxy s21"])

    # 4. Alice is the person who loves stir fry.
    s.add(name_pos["Alice"] == food_pos["stir fry"])

    # 5. The tea drinker is not in the fifth house.
    s.add(drink_pos["tea"] != 5)

    # 6. The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
    left_of(car_pos["bmw 3 series"], drink_pos["tea"])

    # 7. The person who is a doctor is Arnold.
    s.add(occ_pos["doctor"] == name_pos["Arnold"])

    # 8. The person who uses an iPhone 13 is the coffee drinker.
    s.add(phone_pos["iphone 13"] == drink_pos["coffee"])

    # 9. The person who is an engineer is the person who owns a BMW 3 Series.
    s.add(occ_pos["engineer"] == car_pos["bmw 3 series"])

    # 10. The person who loves the stew is the person who uses an iPhone 13.
    s.add(food_pos["stew"] == phone_pos["iphone 13"])

    # 11. The person who is a doctor is directly left of the person who uses a OnePlus 9.
    direct_left(occ_pos["doctor"], phone_pos["oneplus 9"])

    # 12. The person who owns a Honda Civic is directly left of the spaghetti eater.
    direct_left(car_pos["honda civic"], food_pos["spaghetti"])

    # 13. The person who uses a Google Pixel 6 is the tea drinker.
    s.add(phone_pos["google pixel 6"] == drink_pos["tea"])

    # 14. Alice is the person who is an artist.
    s.add(name_pos["Alice"] == occ_pos["artist"])

    # 15. There is one house between Alice and the person who owns a Ford F-150.
    s.add(Or(name_pos["Alice"] - car_pos["ford f150"] == 2, car_pos["ford f150"] - name_pos["Alice"] == 2))

    # 16. Arnold is the person who owns a Toyota Camry.
    s.add(name_pos["Arnold"] == car_pos["toyota camry"])

    # 17. Eric is in the fourth house.
    s.add(name_pos["Eric"] == 4)

    # 18. The person who uses a OnePlus 9 is the person who is a lawyer.
    s.add(phone_pos["oneplus 9"] == occ_pos["lawyer"])

    # 19. The person who loves eating grilled cheese is Peter.
    s.add(food_pos["grilled cheese"] == name_pos["Peter"])

    # Solve
    if s.check() != sat:
        result = {
            "solution": {
                "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    # Build inverse maps: house -> value
    def invert(pos_dict):
        inv = {}
        for k, v in pos_dict.items():
            inv[m.eval(v).as_long()] = k
        return inv

    inv_name = invert(name_pos)
    inv_food = invert(food_pos)
    inv_car = invert(car_pos)
    inv_phone = invert(phone_pos)
    inv_occ = invert(occ_pos)
    inv_drink = invert(drink_pos)

    rows = []
    for h in range(1, 6):
        row = [
            str(h),
            inv_name[h],
            inv_food[h],
            inv_car[h],
            inv_phone[h],
            inv_occ[h],
            inv_drink[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()