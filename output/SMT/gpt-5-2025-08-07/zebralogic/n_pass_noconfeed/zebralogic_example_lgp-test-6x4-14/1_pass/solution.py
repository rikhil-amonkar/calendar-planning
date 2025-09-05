import json
import re
from z3 import Solver, Int, And, Distinct, Or, Abs

def make_var_name(prefix, label):
    safe = re.sub(r'[^A-Za-z0-9_]', '_', label.lower().replace(' ', '_'))
    return f"{prefix}_{safe}"

def setup_vars(prefix, labels):
    return {label: Int(make_var_name(prefix, label)) for label in labels}

def all_in_range(vars_dict, lo, hi):
    return [And(v >= lo, v <= hi) for v in vars_dict.values()]

def invert_mapping(model, vars_dict):
    # returns list indexed by house-1 with the label at that house
    by_pos = [None] * 6
    for label, var in vars_dict.items():
        pos = model.eval(var).as_long()
        by_pos[pos - 1] = label
    return by_pos

def main():
    houses = [1,2,3,4,5,6]
    # Attributes
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    cars = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

    # Create variables: each label maps to house position 1..6
    name_pos = setup_vars('name', names)
    car_pos = setup_vars('car', cars)
    mother_pos = setup_vars('mother', mothers)
    hobby_pos = setup_vars('hobby', hobbies)

    s = Solver()

    # Domain constraints
    s.add(*all_in_range(name_pos, 1, 6))
    s.add(*all_in_range(car_pos, 1, 6))
    s.add(*all_in_range(mother_pos, 1, 6))
    s.add(*all_in_range(hobby_pos, 1, 6))

    # AllDifferent within each category
    s.add(Distinct(*name_pos.values()))
    s.add(Distinct(*car_pos.values))
    s.add(Distinct(*mother_pos.values()))
    s.add(Distinct(*hobby_pos.values()))

    # Helper shortcuts
    pos = {
        'Eric': name_pos['Eric'],
        'Bob': name_pos['Bob'],
        'Peter': name_pos['Peter'],
        'Alice': name_pos['Alice'],
        'Arnold': name_pos['Arnold'],
        'Carol': name_pos['Carol'],

        'ford f150': car_pos['ford f150'],
        'honda civic': car_pos['honda civic'],
        'toyota camry': car_pos['toyota camry'],
        'tesla model 3': car_pos['tesla model 3'],
        'chevrolet silverado': car_pos['chevrolet silverado'],
        'bmw 3 series': car_pos['bmw 3 series'],

        'Sarah': mother_pos['Sarah'],
        'Penny': mother_pos['Penny'],
        'Holly': mother_pos['Holly'],
        'Aniya': mother_pos['Aniya'],
        'Kailyn': mother_pos['Kailyn'],
        'Janelle': mother_pos['Janelle'],

        'photography': hobby_pos['photography'],
        'cooking': hobby_pos['cooking'],
        'knitting': hobby_pos['knitting'],
        'gardening': hobby_pos['gardening'],
        'woodworking': hobby_pos['woodworking'],
        'painting': hobby_pos['painting'],
    }

    # Clues:
    # 1. The person who owns a Toyota Camry is in the sixth house.
    s.add(pos['toyota camry'] == 6)

    # 2. Carol is the photography enthusiast.
    s.add(pos['Carol'] == pos['photography'])

    # 3. The person who owns a Chevrolet Silverado is The person whose mother's name is Aniya.
    s.add(pos['chevrolet silverado'] == pos['Aniya'])

    # 4. The person who owns a Chevrolet Silverado is not in the second house.
    s.add(pos['chevrolet silverado'] != 2)

    # 5. The person who owns a Ford F-150 is The person whose mother's name is Sarah.
    s.add(pos['ford f150'] == pos['Sarah'])

    # 6. The person who owns a BMW 3 Series is Bob.
    s.add(pos['bmw 3 series'] == pos['Bob'])

    # 7. The person whose mother's name is Kailyn is in the sixth house.
    s.add(pos['Kailyn'] == 6)

    # 8. Eric is directly left of the person who enjoys knitting.
    s.add(pos['Eric'] + 1 == pos['knitting'])

    # 9. There is one house between Sarah and the person who owns a Toyota Camry.
    s.add(Abs(pos['Sarah'] - pos['toyota camry']) == 2)

    # 10. The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
    s.add(pos['Penny'] > pos['knitting'])

    # 11. The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
    s.add(pos['Aniya'] > pos['honda civic'])

    # 12. Alice is somewhere to the right of the person who owns a Ford F-150.
    s.add(pos['Alice'] > pos['ford f150'])

    # 13. Eric is the person who enjoys gardening.
    s.add(pos['Eric'] == pos['gardening'])

    # 14. The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    s.add(pos['woodworking'] < pos['knitting'])

    # 15. There is one house between The person whose mother's name is Sarah and the person who loves cooking.
    s.add(Abs(pos['Sarah'] - pos['cooking']) == 2)

    # 16. The person who owns a Honda Civic is Arnold.
    s.add(pos['honda civic'] == pos['Arnold'])

    # 17. The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    s.add(pos['Holly'] + 1 == pos['knitting'])

    # Solve
    if s.check() != 1:
        raise RuntimeError("No solution found")

    m = s.model()

    # Invert mappings to get attributes by house
    names_by_house = invert_mapping(m, name_pos)
    cars_by_house = invert_mapping(m, car_pos)
    mothers_by_house = invert_mapping(m, mother_pos)
    hobbies_by_house = invert_mapping(m, hobby_pos)

    result = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
            "rows": []
        }
    }

    for i in range(6):
        row = [
            str(i + 1),
            names_by_house[i],
            cars_by_house[i],
            mothers_by_house[i],
            hobbies_by_house[i]
        ]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()