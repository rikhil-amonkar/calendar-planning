import json
from z3 import Int, Solver, Distinct, And, Or

def solve_puzzle():
    houses = [1, 2, 3, 4]

    Names = ['Eric', 'Peter', 'Alice', 'Arnold']
    Cars = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    Birthdays = ['jan', 'april', 'sept', 'feb']
    Hobbies = ['painting', 'cooking', 'gardening', 'photography']

    def mk_vars(prefix, keys):
        def sanitize(k): return k.replace(' ', '_')
        return {k: Int(f"{prefix}_{sanitize(k)}") for k in keys}

    name_pos = mk_vars("Name", Names)
    car_pos = mk_vars("Car", Cars)
    bday_pos = mk_vars("Bday", Birthdays)
    hobby_pos = mk_vars("Hobby", Hobbies)

    s = Solver()

    # Domain constraints
    for m in [name_pos, car_pos, bday_pos, hobby_pos]:
        for v in m.values():
            s.add(And(v >= 1, v <= 4))

    # Uniqueness within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([car_pos[c] for c in Cars]))
    s.add(Distinct([bday_pos[b] for b in Birthdays]))
    s.add(Distinct([hobby_pos[h] for h in Hobbies]))

    # Clues:
    # 1. The person whose birthday is in January is not in the second house.
    s.add(bday_pos['jan'] != 2)

    # 2. The photography enthusiast is somewhere to the left of Eric.
    s.add(hobby_pos['photography'] < name_pos['Eric'])

    # 3. The photography enthusiast is somewhere to the left of Peter.
    s.add(hobby_pos['photography'] < name_pos['Peter'])

    # 4. The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    s.add(car_pos['honda civic'] + 1 == car_pos['tesla model 3'])

    # 5. There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    s.add(Or(car_pos['tesla model 3'] == hobby_pos['gardening'] + 2,
             car_pos['tesla model 3'] == hobby_pos['gardening'] - 2))

    # 6. The person who owns a Tesla Model 3 is Arnold.
    s.add(car_pos['tesla model 3'] == name_pos['Arnold'])

    # 7. The person whose birthday is in February is the person who loves cooking.
    s.add(bday_pos['feb'] == hobby_pos['cooking'])

    # 8. The person who owns a Toyota Camry is Peter.
    s.add(car_pos['toyota camry'] == name_pos['Peter'])

    # 9. The person whose birthday is in April is Arnold.
    s.add(bday_pos['april'] == name_pos['Arnold'])

    # 10. Alice is the photography enthusiast.
    s.add(name_pos['Alice'] == hobby_pos['photography'])

    # 11. Peter is the person whose birthday is in January.
    s.add(name_pos['Peter'] == bday_pos['jan'])

    assert s.check().r == 1  # sat

    model = s.model()

    def invert(mapping):
        inv = {}
        for k, v in mapping.items():
            inv[model[v].as_long()] = k
        return inv

    inv_names = invert(name_pos)
    inv_cars = invert(car_pos)
    inv_bdays = invert(bday_pos)
    inv_hobbies = invert(hobby_pos)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_names[h],
            inv_cars[h],
            inv_bdays[h],
            inv_hobbies[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()