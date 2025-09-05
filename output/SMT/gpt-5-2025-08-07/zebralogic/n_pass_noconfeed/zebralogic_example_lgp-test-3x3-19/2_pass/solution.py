import json
from z3 import Solver, Int, Distinct, And, sat

def solve_puzzle():
    houses = [1, 2, 3]

    # Variables: positions (house indices) for each attribute value
    names = {
        'Eric': Int('Eric'),
        'Arnold': Int('Arnold'),
        'Peter': Int('Peter')
    }

    smoothies = {
        'desert': Int('desert'),
        'watermelon': Int('watermelon'),
        'cherry': Int('cherry')
    }

    books = {
        'science fiction': Int('science_fiction'),
        'romance': Int('romance'),
        'mystery': Int('mystery')
    }

    s = Solver()

    # Domain constraints: all positions are in 1..3
    for var in list(names.values()) + list(smoothies.values()) + list(books.values()):
        s.add(And(var >= 1, var <= 3))

    # Uniqueness within each category
    s.add(Distinct(*names.values()))
    s.add(Distinct(*smoothies.values()))
    s.add(Distinct(*books.values()))

    # Clues:
    # 1. Cherry smoothie is somewhere to the left of the person who loves mystery books.
    s.add(smoothies['cherry'] < books['mystery'])

    # 2. Arnold is the person who loves mystery books.
    s.add(names['Arnold'] == books['mystery'])

    # 3. Science fiction is not in the first house.
    s.add(books['science fiction'] != 1)

    # 4. Desert smoothie lover is directly left of the person who loves mystery books.
    s.add(smoothies['desert'] + 1 == books['mystery'])

    # 5. Peter is in the first house.
    s.add(names['Peter'] == 1)

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    def get_at_house(mapping, house):
        for k, v in mapping.items():
            if m[v].as_long() == house:
                return k
        return None

    header = ["House", "Name", "Smoothie", "BookGenre"]
    rows = []
    for h in houses:
        row = [
            str(h),
            get_at_house(names, h),
            get_at_house(smoothies, h),
            get_at_house(books, h)
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
    print(json.dumps(solution, ensure_ascii=False, indent=2))