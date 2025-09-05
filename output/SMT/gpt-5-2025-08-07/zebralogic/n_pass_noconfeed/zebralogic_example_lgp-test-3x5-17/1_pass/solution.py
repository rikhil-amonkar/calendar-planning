import json
from z3 import Solver, Int, And, Distinct, sat

def main():
    houses = [1, 2, 3]

    # Define variables: each attribute value is mapped to a house index (1..3)
    names = {
        "Eric": Int("Eric"),
        "Arnold": Int("Arnold"),
        "Peter": Int("Peter"),
    }
    phones = {
        "iphone 13": Int("iphone_13"),
        "samsung galaxy s21": Int("samsung_galaxy_s21"),
        "google pixel 6": Int("google_pixel_6"),
    }
    heights = {
        "very short": Int("very_short"),
        "average": Int("average"),
        "short": Int("short"),
    }
    styles = {
        "colonial": Int("colonial"),
        "ranch": Int("ranch"),
        "victorian": Int("victorian"),
    }
    cars = {
        "tesla model 3": Int("tesla_model_3"),
        "toyota camry": Int("toyota_camry"),
        "ford f150": Int("ford_f150"),
    }

    # Collect all variables
    all_vars = []
    for d in (names, phones, heights, styles, cars):
        all_vars.extend(d.values())

    s = Solver()

    # Domain constraints: each variable is a house index in 1..3
    for v in all_vars:
        s.add(And(v >= 1, v <= 3))

    # Uniqueness constraints within each category
    s.add(Distinct(*names.values()))
    s.add(Distinct(*phones.values()))
    s.add(Distinct(*heights.values()))
    s.add(Distinct(*styles.values()))
    s.add(Distinct(*cars.values()))

    # Clues:
    # 1. Peter is somewhere to the right of Eric.
    s.add(names["Peter"] > names["Eric"])

    # 2. The person living in a colonial-style house is in the second house.
    s.add(styles["colonial"] == 2)

    # 3. The person who owns a Tesla Model 3 is the person who is very short.
    s.add(cars["tesla model 3"] == heights["very short"])

    # 4. The person who is short is directly left of the person who uses a Samsung Galaxy S21.
    s.add(heights["short"] + 1 == phones["samsung galaxy s21"])

    # 5. The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
    s.add(phones["iphone 13"] + 1 == phones["google pixel 6"])

    # 6. The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
    s.add(styles["colonial"] > styles["ranch"])

    # 7. Arnold is in the second house.
    s.add(names["Arnold"] == 2)

    # 8. The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
    s.add(cars["ford f150"] > cars["toyota camry"])

    # 9. The person who has an average height is in the first house.
    s.add(heights["average"] == 1)

    # Solve
    if s.check() != sat:
        raise RuntimeError("Puzzle constraints are unsatisfiable.")
    m = s.model()

    # Helper to invert mapping: house -> attribute value label
    def invert(category_dict):
        inv = {}
        for label, var in category_dict.items():
            h = m[var].as_long()
            inv[h] = label
        return inv

    inv_names = invert(names)
    inv_phones = invert(phones)
    inv_heights = invert(heights)
    inv_styles = invert(styles)
    inv_cars = invert(cars)

    header = ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"]
    rows = []
    for h in houses:
        row = [
            str(h),
            inv_names[h],
            inv_phones[h],
            inv_heights[h],
            inv_styles[h],
            inv_cars[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()