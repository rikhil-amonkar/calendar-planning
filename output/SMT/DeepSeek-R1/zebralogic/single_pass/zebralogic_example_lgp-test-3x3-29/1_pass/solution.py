from z3 import *
import json

def main():
    # Define enums for attributes
    NameEnum, (Eric, Peter, Arnold) = EnumSort('NameEnum', ['Eric', 'Peter', 'Arnold'])
    MotherEnum, (Holly, Aniya, Janelle) = EnumSort('MotherEnum', ['Holly', 'Aniya', 'Janelle'])
    FoodEnum, (Pizza, GrilledCheese, Spaghetti) = EnumSort('FoodEnum', ['Pizza', 'GrilledCheese', 'Spaghetti'])

    # Variables for each house (0: house1, 1: house2, 2: house3)
    names = [Const(f'n{i}', NameEnum) for i in range(3)]
    mothers = [Const(f'm{i}', MotherEnum) for i in range(3)]
    foods = [Const(f'f{i}', FoodEnum) for i in range(3)]

    s = Solver()

    # All attributes are distinct
    s.add(Distinct(names))
    s.add(Distinct(mothers))
    s.add(Distinct(foods))

    # Clue 1: Spaghetti eater and Peter are adjacent
    s.add(Or(
        And(names[0] == Peter, foods[1] == Spaghetti),
        And(names[1] == Peter, Or(foods[0] == Spaghetti, foods[2] == Spaghetti)),
        And(names[2] == Peter, foods[1] == Spaghetti)
    ))

    # Clue 2: Grilled cheese eater is directly left of Aniya's mother
    s.add(Or(
        And(foods[0] == GrilledCheese, mothers[1] == Aniya),
        And(foods[1] == GrilledCheese, mothers[2] == Aniya)
    ))

    # Clue 3: Grilled cheese eater is Eric
    for i in range(3):
        s.add(Implies(foods[i] == GrilledCheese, names[i] == Eric))

    # Clue 4: Peter's mother is Holly
    for i in range(3):
        s.add(Implies(names[i] == Peter, mothers[i] == Holly))

    # Solve and get the model
    if s.check() == sat:
        model = s.model()
        food_mapping = {
            'Pizza': 'pizza',
            'GrilledCheese': 'grilled cheese',
            'Spaghetti': 'spaghetti'
        }
        rows = []
        for i in range(3):
            house = str(i + 1)
            n_val = model.eval(names[i])
            m_val = model.eval(mothers[i])
            f_val = model.eval(foods[i])
            n_str = str(n_val)
            m_str = str(m_val)
            f_str = str(f_val)
            f_out = food_mapping.get(f_str, f_str)
            rows.append([house, n_str, m_str, f_out])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Mother", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()