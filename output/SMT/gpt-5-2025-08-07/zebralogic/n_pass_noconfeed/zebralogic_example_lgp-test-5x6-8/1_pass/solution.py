from z3 import *
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    Names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
    HouseStyles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
    Mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
    PhoneModels = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
    Drinks = ["coffee", "water", "root beer", "tea", "milk"]
    Animals = ["fish", "dog", "horse", "bird", "cat"]

    # Create Z3 variables for positions of each attribute value
    def create_vars(items, prefix):
        return {item: Int(f"{prefix}_{i}") for i, item in enumerate(items)}

    pos_name = create_vars(Names, "name")
    pos_style = create_vars(HouseStyles, "style")
    pos_mother = create_vars(Mothers, "mother")
    pos_phone = create_vars(PhoneModels, "phone")
    pos_drink = create_vars(Drinks, "drink")
    pos_animal = create_vars(Animals, "animal")

    s = Solver()

    # Each position is between 1 and 5
    for group in [pos_name, pos_style, pos_mother, pos_phone, pos_drink, pos_animal]:
        for var in group.values():
            s.add(And(var >= 1, var <= 5))
        s.add(Distinct(list(group.values())))

    # Clues as constraints

    # 1. The person who uses a Google Pixel 6 is not in the first house.
    s.add(pos_phone["google pixel 6"] != 1)

    # 2. The one who only drinks water is Alice.
    s.add(pos_drink["water"] == pos_name["Alice"])

    # 3. The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
    s.add(pos_style["colonial"] > pos_phone["huawei p50"])

    # 4. The person who keeps horses is the person who uses a OnePlus 9.
    s.add(pos_animal["horse"] == pos_phone["oneplus 9"])

    # 5. The person in a ranch-style home is The person whose mother's name is Kailyn.
    s.add(pos_style["ranch"] == pos_mother["Kailyn"])

    # 6. The root beer lover is the cat lover.
    s.add(pos_drink["root beer"] == pos_animal["cat"])

    # 7. The person living in a colonial-style house is not in the fourth house.
    s.add(pos_style["colonial"] != 4)

    # 8. The bird keeper is in the fourth house.
    s.add(pos_animal["bird"] == 4)

    # 9. The tea drinker is Bob.
    s.add(pos_drink["tea"] == pos_name["Bob"])

    # 10. The tea drinker is somewhere to the right of The person whose mother's name is Kailyn.
    s.add(pos_drink["tea"] > pos_mother["Kailyn"])

    # 11. The root beer lover is somewhere to the left of The person whose mother's name is Kailyn.
    s.add(pos_drink["root beer"] < pos_mother["Kailyn"])

    # 12. The person who keeps horses is the person in a modern-style house.
    s.add(pos_animal["horse"] == pos_style["modern"])

    # 13. The person who uses an iPhone 13 is the person who likes milk.
    s.add(pos_phone["iphone 13"] == pos_drink["milk"])

    # 14. The dog owner is the person who likes milk.
    s.add(pos_animal["dog"] == pos_drink["milk"])

    # 15. The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
    s.add(pos_phone["google pixel 6"] == pos_style["craftsman"])

    # 16. Eric is not in the second house.
    s.add(pos_name["Eric"] != 2)

    # 17. The tea drinker is in the fourth house.
    s.add(pos_drink["tea"] == 4)

    # 18. The person who keeps horses is in the third house.
    s.add(pos_animal["horse"] == 3)

    # 19. The person in a modern-style house is The person whose mother's name is Penny.
    s.add(pos_style["modern"] == pos_mother["Penny"])

    # 20. The root beer lover is Peter.
    s.add(pos_drink["root beer"] == pos_name["Peter"])

    # 21. The person whose mother's name is Aniya is not in the fourth house.
    s.add(pos_mother["Aniya"] != 4)

    # 22. The person whose mother's name is Janelle is the one who only drinks water.
    s.add(pos_mother["Janelle"] == pos_drink["water"])

    if s.check() != sat:
        return {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                "rows": []
            }
        }

    m = s.model()

    # Helper to invert mapping from item->position to position->item
    def invert(group):
        inv = {}
        for item, var in group.items():
            inv[m.evaluate(var).as_long()] = item
        return inv

    inv_name = invert(pos_name)
    inv_style = invert(pos_style)
    inv_mother = invert(pos_mother)
    inv_phone = invert(pos_phone)
    inv_drink = invert(pos_drink)
    inv_animal = invert(pos_animal)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_name[h],
            inv_style[h],
            inv_mother[h],
            inv_phone[h],
            inv_drink[h],
            inv_animal[h]
        ]
        rows.append(row)

    return {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))