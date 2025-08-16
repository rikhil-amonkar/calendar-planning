from z3 import *
import json

def main():
    # Define the enums and the mapping to display strings.
    Name, (Eric, Arnold, Peter) = EnumSort('Name', ['Eric','Arnold','Peter'])
    name_map = { Eric: 'Eric', Arnold: 'Arnold', Peter: 'Peter' }

    Vacation, (mountain, city, beach) = EnumSort('Vacation', ['mountain','city','beach'])
    vacation_map = { mountain: 'mountain', city: 'city', beach: 'beach' }

    Height, (very_short, short, average) = EnumSort('Height', ['very_short','short','average'])
    height_map = { very_short: 'very short', short: 'short', average: 'average' }

    Flower, (carnations, daffodils, lilies) = EnumSort('Flower', ['carnations','daffodils','lilies'])
    flower_map = { carnations: 'carnations', daffodils: 'daffodils', lilies: 'lilies' }

    HairColor, (brown, black, blonde) = EnumSort('HairColor', ['brown','black','blonde'])
    hair_map = { brown: 'brown', black: 'black', blonde: 'blonde' }

    Education, (associate, bachelor, high_school) = EnumSort('Education', ['associate','bachelor','high_school'])
    education_map = { associate: 'associate', bachelor: 'bachelor', high_school: 'high school' }

    # Variables for the three houses (index0: house1, index1: house2, index2: house3)
    n = [Const('n0', Name), Const('n1', Name), Const('n2', Name)]
    v = [Const('v0', Vacation), Const('v1', Vacation), Const('v2', Vacation)]
    ht = [Const('ht0', Height), Const('ht1', Height), Const('ht2', Height)]
    f = [Const('f0', Flower), Const('f1', Flower), Const('f2', Flower)]
    hc = [Const('hc0', HairColor), Const('hc1', HairColor), Const('hc2', HairColor)]
    e = [Const('e0', Education), Const('e1', Education), Const('e2', Education)]

    s = Solver()

    # All attributes are distinct per house
    s.add(Distinct(n))
    s.add(Distinct(v))
    s.add(Distinct(ht))
    s.add(Distinct(f))
    s.add(Distinct(hc))
    s.add(Distinct(e))

    # Clue 1: Peter is the person who has an average height.
    for i in range(3):
        s.add(Implies(n[i] == Peter, ht[i] == average))

    # Clue 2: The person who loves a bouquet of daffodils is Arnold.
    for i in range(3):
        s.add(Implies(f[i] == daffodils, n[i] == Arnold))

    # Clue 3: The person who is very short is not in the second house.
    s.add(ht[1] != very_short)

    # Clue 4: The person who loves beach vacations is in the first house.
    s.add(v[0] == beach)

    # Clue 5: The person with a high school diploma is in the third house.
    s.add(e[2] == high_school)

    # Clue 6: The person who is short is somewhere to the right of the person who is very short.
    vs_index = Int('vs_index')
    s.add(vs_index >= 0, vs_index <= 2)
    for i in range(3):
        s.add(If(ht[i] == very_short, vs_index == i, True))
    s.add(Or(ht[0] == very_short, ht[1] == very_short, ht[2] == very_short))

    s_index = Int('s_index')
    s.add(s_index >= 0, s_index <= 2)
    for i in range(3):
        s.add(If(ht[i] == short, s_index == i, True))
    s.add(Or(ht[0] == short, ht[1] == short, ht[2] == short))

    s.add(s_index > vs_index)

    # Clue 7: The person who loves the boquet of lilies is Eric.
    for i in range(3):
        s.add(Implies(f[i] == lilies, n[i] == Eric))

    # Clue 8: The person who loves the boquet of lilies is the person with a bachelor's degree.
    for i in range(3):
        s.add(Implies(f[i] == lilies, e[i] == bachelor))

    # Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
    peter_house = Int('peter_house')
    s.add(peter_house >= 0, peter_house <= 2)
    for i in range(3):
        s.add(If(n[i] == Peter, peter_house == i, True))

    city_house = Int('city_house')
    s.add(city_house >= 0, city_house <= 2)
    for i in range(3):
        s.add(If(v[i] == city, city_house == i, True))

    s.add(city_house > peter_house)

    # Clue 10: The person who has blonde hair is in the third house.
    s.add(hc[2] == blonde)

    # Clue 11: The person who loves beach vacations is the person who has brown hair.
    for i in range(3):
        s.add(Implies(v[i] == beach, hc[i] == brown))

    # Now check and get model
    if s.check() == sat:
        m = s.model()

        # Build the rows for the houses
        rows = []
        for i in range(3):
            house_num = str(i+1)
            name_val = name_map[m.eval(n[i])]
            vac_val = vacation_map[m.eval(v[i])]
            ht_val = height_map[m.eval(ht[i])]
            flower_val = flower_map[m.eval(f[i])]
            hair_val = hair_map[m.eval(hc[i])]
            edu_val = education_map[m.eval(e[i])]

            row = [house_num, name_val, vac_val, ht_val, flower_val, hair_val, edu_val]
            rows.append(row)

        # Build the solution dictionary
        solution_dict = {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": rows
        }

        output_dict = {
            "solution": solution_dict
        }

        # Print the JSON string
        print(json.dumps(output_dict, indent=2))

    else:
        print("No solution found")

if __name__ == "__main__":
    main()