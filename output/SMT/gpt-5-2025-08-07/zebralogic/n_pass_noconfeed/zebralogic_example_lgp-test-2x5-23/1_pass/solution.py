import json
from z3 import Solver, Ints, And, Or, Distinct

def solve_puzzle():
    # Houses indexed 0..1 represent houses 1..2
    num_houses = 2
    houses = list(range(num_houses))

    # Domains
    Names = ["Arnold", "Eric"]
    Educations = ["associate", "high school"]
    Heights = ["short", "very short"]
    Foods = ["grilled cheese", "pizza"]
    Drinks = ["tea", "water"]

    # Index helpers
    name_idx = {v: i for i, v in enumerate(Names)}
    edu_idx = {v: i for i, v in enumerate(Educations)}
    height_idx = {v: i for i, v in enumerate(Heights)}
    food_idx = {v: i for i, v in enumerate(Foods)}
    drink_idx = {v: i for i, v in enumerate(Drinks)}

    # Variables: per house assignment for each attribute
    N0, N1 = Ints('Name_1 Name_2')
    E0, E1 = Ints('Education_1 Education_2')
    H0, H1 = Ints('Height_1 Height_2')
    F0, F1 = Ints('Food_1 Food_2')
    D0, D1 = Ints('Drink_1 Drink_2')

    name_vars = [N0, N1]
    edu_vars = [E0, E1]
    height_vars = [H0, H1]
    food_vars = [F0, F1]
    drink_vars = [D0, D1]

    s = Solver()

    # Domain constraints: each attribute is a permutation of its domain (0..1)
    for arr in [name_vars, edu_vars, height_vars, food_vars, drink_vars]:
        for v in arr:
            s.add(And(v >= 0, v < 2))
        s.add(Distinct(arr))

    # Helper to assert "the person who is A=va is the same person who is B=vb"
    def same_person(arrA, va_idx, arrB, vb_idx):
        s.add(Or(*[And(arrA[i] == va_idx, arrB[i] == vb_idx) for i in houses]))

    # Clues:
    # 1. The person who is very short is the person who is a pizza lover.
    same_person(height_vars, height_idx["very short"], food_vars, food_idx["pizza"])

    # 2. The person who loves eating grilled cheese is in the second house.
    s.add(food_vars[1] == food_idx["grilled cheese"])

    # 3. The person with a high school diploma is the person who is a pizza lover.
    same_person(edu_vars, edu_idx["high school"], food_vars, food_idx["pizza"])

    # 4. The tea drinker is the person who loves eating grilled cheese.
    same_person(drink_vars, drink_idx["tea"], food_vars, food_idx["grilled cheese"])

    # 5. Arnold is the person who is a pizza lover.
    same_person(name_vars, name_idx["Arnold"], food_vars, food_idx["pizza"])

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Extract solution
    rows = []
    for i in houses:
        name_val = Names[m.eval(name_vars[i]).as_long()]
        edu_val = Educations[m.eval(edu_vars[i]).as_long()]
        height_val = Heights[m.eval(height_vars[i]).as_long()]
        food_val = Foods[m.eval(food_vars[i]).as_long()]
        drink_val = Drinks[m.eval(drink_vars[i]).as_long()]
        rows.append([str(i + 1), name_val, edu_val, height_val, food_val, drink_val])

    result = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))