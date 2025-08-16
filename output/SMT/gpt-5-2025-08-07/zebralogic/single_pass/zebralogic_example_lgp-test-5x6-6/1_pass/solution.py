import json
from z3 import Solver, Int, Distinct, And, Or, Abs

def solve_puzzle():
    houses = range(1, 6)

    # Categories and items (use exact strings required)
    Names = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
    Vacations = ['mountain', 'city', 'cruise', 'beach', 'camping']
    Educations = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
    Colors = ['blue', 'red', 'white', 'yellow', 'green']
    Phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
    Foods = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']

    # Create Z3 variables: position (house index) for each item in each category
    def mk_vars(items):
        return {item: Int(item.replace(' ', '_')) for item in items}

    pos_name = mk_vars(Names)
    pos_vac = mk_vars(Vacations)
    pos_edu = mk_vars(Educations)
    pos_color = mk_vars(Colors)
    pos_phone = mk_vars(Phones)
    pos_food = mk_vars(Foods)

    s = Solver()

    # Domain constraints: all positions between 1 and 5
    for d in [pos_name, pos_vac, pos_edu, pos_color, pos_phone, pos_food]:
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # AllDifferent per category
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_vac.values))
    s.add(Distinct(*pos_vac.values()))
    s.add(Distinct(*pos_edu.values()))
    s.add(Distinct(*pos_color.values()))
    s.add(Distinct(*pos_phone.values()))
    s.add(Distinct(*pos_food.values()))

    # Clues encoding:
    # 1. The person who loves the stew is not in the first house.
    s.add(pos_food['stew'] != 1)

    # 2. Two houses between the stir fry lover and the associate's degree.
    s.add(Abs(pos_food['stir_fry'] - pos_edu['associate']) == 3)

    # 3. Mountain retreats = bachelor's degree.
    s.add(pos_vac['mountain'] == pos_edu['bachelor'])

    # 4. Doctorate to the right of Bob.
    s.add(pos_edu['doctorate'] > pos_name['Bob'])

    # 5. Samsung Galaxy S21 is in the third house.
    s.add(pos_phone['samsung_galaxy_s21'] == 3)

    # 6. Eric has the doctorate.
    s.add(pos_name['Eric'] == pos_edu['doctorate'])

    # 7. Doctorate is in the third house.
    s.add(pos_edu['doctorate'] == 3)

    # 8. Stir fry = bachelor's degree.
    s.add(pos_food['stir_fry'] == pos_edu['bachelor'])

    # 9. Doctorate = pizza lover.
    s.add(pos_edu['doctorate'] == pos_food['pizza'])

    # 10. Green is to the right of Peter.
    s.add(pos_color['green'] > pos_name['Peter'])

    # 11. Camping = iPhone 13.
    s.add(pos_vac['camping'] == pos_phone['iphone_13'])

    # 12. Cruises = Alice.
    s.add(pos_vac['cruise'] == pos_name['Alice'])

    # 13. One house between high school and S21 (i.e., distance 2).
    s.add(Abs(pos_edu['high_school'] - pos_phone['samsung_galaxy_s21']) == 2)

    # 14. Google Pixel 6 = Arnold.
    s.add(pos_phone['google_pixel_6'] == pos_name['Arnold'])

    # 15. OnePlus 9 right of Huawei P50.
    s.add(pos_phone['oneplus_9'] > pos_phone['huawei_p50'])

    # 16. Arnold loves grilled cheese.
    s.add(pos_name['Arnold'] == pos_food['grilled_cheese'])

    # 17. Grilled cheese not in the fourth house.
    s.add(pos_food['grilled_cheese'] != 4)

    # 18. Two houses between bachelor's degree and red.
    s.add(Abs(pos_edu['bachelor'] - pos_color['red']) == 3)

    # 19. Beach right of city.
    s.add(pos_vac['beach'] > pos_vac['city'])

    # 20. Green not in the second house.
    s.add(pos_color['green'] != 2)

    # 21. Blue right of Peter.
    s.add(pos_color['blue'] > pos_name['Peter'])

    # 22. One house between camping and yellow (distance 2).
    s.add(Abs(pos_vac['camping'] - pos_color['yellow']) == 2)

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Helper to invert mapping: house -> item for a category
    def invert(pos_dict, original_items):
        house_to_item = {}
        for item in original_items:
            v = pos_dict[item.replace(' ', '_')] if ' ' in item else pos_dict[item]
            house = m[v].as_long()
            house_to_item[house] = item
        return house_to_item

    # Because we used underscores in variable names for items with spaces
    # build pos_dicts with those exact variable names
    # Rebuild dictionaries (name -> var) with standardized keys used above
    pos_dict_actual = {
        'Name': {k: pos_name[k] for k in Names},
        'Vacation': {
            'mountain': pos_vac['mountain'],
            'city': pos_vac['city'],
            'cruise': pos_vac['cruise'],
            'beach': pos_vac['beach'],
            'camping': pos_vac['camping'],
        },
        'Education': {
            'doctorate': pos_edu['doctorate'],
            'high school': pos_edu['high_school'],
            'bachelor': pos_edu['bachelor'],
            'associate': pos_edu['associate'],
            'master': pos_edu['master'],
        },
        'Color': {
            'blue': pos_color['blue'],
            'red': pos_color['red'],
            'white': pos_color['white'],
            'yellow': pos_color['yellow'],
            'green': pos_color['green'],
        },
        'PhoneModel': {
            'google pixel 6': pos_phone['google_pixel_6'],
            'iphone 13': pos_phone['iphone_13'],
            'oneplus 9': pos_phone['oneplus_9'],
            'huawei p50': pos_phone['huawei_p50'],
            'samsung galaxy s21': pos_phone['samsung_galaxy_s21'],
        },
        'Food': {
            'grilled cheese': pos_food['grilled_cheese'],
            'stir fry': pos_food['stir_fry'],
            'pizza': pos_food['pizza'],
            'spaghetti': pos_food['spaghetti'],
            'stew': pos_food['stew'],
        }
    }

    # Invert each category to house->value
    inv = {cat: {} for cat in pos_dict_actual}
    for cat, mapping in pos_dict_actual.items():
        for item, var in mapping.items():
            inv[cat][m[var].as_long()] = item

    header = ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"]
    rows = []
    for h in houses:
        row = [
            str(h),
            inv['Name'][h],
            inv['Vacation'][h],
            inv['Education'][h],
            inv['Color'][h],
            inv['PhoneModel'][h],
            inv['Food'][h]
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))