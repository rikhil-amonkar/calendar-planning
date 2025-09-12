import json
from z3 import *

def main():
    s = Solver()

    # Variables for each house (1, 2, 3) for name, mother, food
    names = [Int(f'name_{i+1}') for i in range(3)]
    mothers = [Int(f'mother_{i+1}') for i in range(3)]
    foods = [Int(f'food_{i+1}') for i in range(3)]

    # All values must be in their respective ranges
    for i in range(3):
        s.add(And(0 <= names[i], names[i] <= 2))
        s.add(And(0 <= mothers[i], mothers[i] <= 2))
        s.add(And(0 <= foods[i], foods[i] <= 2))

    # All distinct per category
    s.add(Distinct(names))
    s.add(Distinct(mothers))
    s.add(Distinct(foods))

    # Clue 3: Eric (name 0) has food grilled cheese (1)
    for i in range(3):
        s.add(Implies(names[i] == 0, foods[i] == 1))

    # Clue 4: Peter (name 1) has mother Holly (0)
    for i in range(3):
        s.add(Implies(names[i] == 1, mothers[i] == 0))

    # Clue 2: Grilled cheese (Eric's food) is directly left of mother Aniya (1)
    s.add(Implies(names[0] == 0, mothers[1] == 1))  # house 1 (index 0) -> house 2 (index 1)
    s.add(Implies(names[1] == 0, mothers[2] == 1))  # house 2 (index 1) -> house 3 (index 2)
    s.add(Implies(names[2] == 0, False))  # house 3 can't have Eric

    # Clue 1: Spaghetti and Peter are adjacent
    spaghetti_house = If(foods[0] == 2, 1, If(foods[1] == 2, 2, 3))
    peter_house = If(names[0] == 1, 1, If(names[1] == 1, 2, 3))
    s.add(Abs(spaghetti_house - peter_house) == 1)

    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            house_num = i + 1
            name_val = m[names[i]].as_long()
            mother_val = m[mothers[i]].as_long()
            food_val = m[foods[i]].as_long()
            name_str = {0: 'Eric', 1: 'Peter', 2: 'Arnold'}[name_val]
            mother_str = {0: 'Holly', 1: 'Aniya', 2: 'Janelle'}[mother_val]
            food_str = {0: 'pizza', 1: 'grilled cheese', 2: 'spaghetti'}[food_val]
            rows.append([str(house_num), name_str, mother_str, food_str])
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()