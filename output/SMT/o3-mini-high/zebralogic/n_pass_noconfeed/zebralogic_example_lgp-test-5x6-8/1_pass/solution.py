from z3 import Solver, Int, And, Distinct, sat
import json

def main():
    solver = Solver()

    # Define variables for each attribute as integers (houses 1 to 5)
    names = {n: Int(n) for n in ["Eric", "Peter", "Arnold", "Bob", "Alice"]}
    styles = {s: Int(s) for s in ["modern", "craftsman", "ranch", "victorian", "colonial"]}
    mothers = {m: Int(m) for m in ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]}
    # Use underscores in keys to avoid spaces in variable names.
    phones = {p: Int(p) for p in ["oneplus_9", "google_pixel_6", "huawei_p50", "iphone_13", "samsung_galaxy_s21"]}
    drinks = {d: Int(d) for d in ["coffee", "water", "root_beer", "tea", "milk"]}
    animals = {a: Int(a) for a in ["fish", "dog", "horse", "bird", "cat"]}

    # All variables must be in range 1 to 5 and be all different within each category.
    categories = [names, styles, mothers, phones, drinks, animals]
    for cat in categories:
        for var in cat.values():
            solver.add(var >= 1, var <= 5)
        solver.add(Distinct(list(cat.values())))

    # Clue 1: The person who uses a Google Pixel 6 is not in the first house.
    solver.add(phones["google_pixel_6"] != 1)
    # Clue 2: The one who only drinks water is Alice.
    solver.add(names["Alice"] == drinks["water"])
    # Clue 3: The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
    solver.add(styles["colonial"] > phones["huawei_p50"])
    # Clue 4: The person who keeps horses is the person who uses a OnePlus 9.
    solver.add(animals["horse"] == phones["oneplus_9"])
    # Clue 5: The person in a ranch-style home is the person whose mother's name is Kailyn.
    solver.add(styles["ranch"] == mothers["Kailyn"])
    # Clue 6: The root beer lover is the cat lover.
    solver.add(drinks["root_beer"] == animals["cat"])
    # Clue 7: The person living in a colonial-style house is not in the fourth house.
    solver.add(styles["colonial"] != 4)
    # Clue 8: The bird keeper is in the fourth house.
    solver.add(animals["bird"] == 4)
    # Clue 9: The tea drinker is Bob.
    solver.add(drinks["tea"] == names["Bob"])
    # Clue 10: The tea drinker is somewhere to the right of the person whose mother's name is Kailyn.
    solver.add(drinks["tea"] > mothers["Kailyn"])
    # Clue 11: The root beer lover is somewhere to the left of the person whose mother's name is Kailyn.
    solver.add(drinks["root_beer"] < mothers["Kailyn"])
    # Clue 12: The person who keeps horses is the person in a modern-style house.
    solver.add(animals["horse"] == styles["modern"])
    # Clue 13: The person who uses an iPhone 13 is the person who likes milk.
    solver.add(phones["iphone_13"] == drinks["milk"])
    # Clue 14: The dog owner is the person who likes milk.
    solver.add(animals["dog"] == drinks["milk"])
    # Clue 15: The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
    solver.add(phones["google_pixel_6"] == styles["craftsman"])
    # Clue 16: Eric is not in the second house.
    solver.add(names["Eric"] != 2)
    # Clue 17: The tea drinker is in the fourth house.
    solver.add(drinks["tea"] == 4)
    # Clue 18: The person who keeps horses is in the third house.
    solver.add(animals["horse"] == 3)
    # Clue 19: The person in a modern-style house is the person whose mother's name is Penny.
    solver.add(styles["modern"] == mothers["Penny"])
    # Clue 20: The root beer lover is Peter.
    solver.add(drinks["root_beer"] == names["Peter"])
    # Clue 21: The person whose mother's name is Aniya is not in the fourth house.
    solver.add(mothers["Aniya"] != 4)
    # Clue 22: The person whose mother's name is Janelle is the one who only drinks water.
    solver.add(mothers["Janelle"] == drinks["water"])

    # Solve the puzzle.
    if solver.check() == sat:
        m = solver.model()
        # Build the solution table row by row (houses 1 to 5).
        solution_rows = []
        for house in range(1, 6):
            # Find the attribute that has the given house number.
            name_val = [k for k, var in names.items() if m[var].as_long() == house][0]
            style_val = [k for k, var in styles.items() if m[var].as_long() == house][0]
            mother_val = [k for k, var in mothers.items() if m[var].as_long() == house][0]
            phone_key = [k for k, var in phones.items() if m[var].as_long() == house][0]
            drink_key = [k for k, var in drinks.items() if m[var].as_long() == house][0]
            animal_val = [k for k, var in animals.items() if m[var].as_long() == house][0]

            # Convert phone and drink keys to match the desired output format.
            phone_conversion = {
                "oneplus_9": "oneplus 9",
                "google_pixel_6": "google pixel 6",
                "huawei_p50": "huawei p50",
                "iphone_13": "iphone 13",
                "samsung_galaxy_s21": "samsung galaxy s21"
            }
            drink_conversion = {
                "coffee": "coffee",
                "water": "water",
                "root_beer": "root beer",
                "tea": "tea",
                "milk": "milk"
            }
            phone_val = phone_conversion[phone_key]
            drink_val = drink_conversion[drink_key]

            solution_rows.append([
                str(house),
                name_val,
                style_val,
                mother_val,
                phone_val,
                drink_val,
                animal_val
            ])

        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()