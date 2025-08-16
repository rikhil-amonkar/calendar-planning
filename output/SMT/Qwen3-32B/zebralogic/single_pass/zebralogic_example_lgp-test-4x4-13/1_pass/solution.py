from z3 import *
import json

def main():
    solver = Solver()

    # Define variables for each house (1-4)
    names = [Int(f'name_{i+1}') for i in range(4)]
    cigars = [Int(f'cigar_{i+1}') for i in range(4)]
    sports = [Int(f'sport_{i+1}') for i in range(4)]
    drinks = [Int(f'drink_{i+1}') for i in range(4)]

    # Add range constraints
    for i in range(4):
        solver.add(And(0 <= names[i], names[i] <= 3))
        solver.add(And(0 <= cigars[i], cigars[i] <= 3))
        solver.add(And(0 <= sports[i], sports[i] <= 3))
        solver.add(And(0 <= drinks[i], drinks[i] <= 3))

    # Add distinct constraints
    solver.add(Distinct(names))
    solver.add(Distinct(cigars))
    solver.add(Distinct(sports))
    solver.add(Distinct(drinks))

    # Clue 1: Peter is in the fourth house (index 3)
    solver.add(names[3] == 1)

    # Clue 10: Peter smokes Pall Mall (3)
    solver.add(cigars[3] == 3)

    # Clue 3: Arnold (2) smokes Blue Master (2)
    for i in range(4):
        solver.add(Implies(names[i] == 2, cigars[i] == 2))

    # Clue 7: Arnold drinks coffee (0)
    for i in range(4):
        solver.add(Implies(names[i] == 2, drinks[i] == 0))

    # Clue 8: house 3 (index 2) has sport 1 (basketball)
    solver.add(sports[2] == 1)

    # Clue 4: the person with sport 1 is Eric (3)
    solver.add(names[2] == 3)

    # Clue 2: sport 1 drinks tea (3)
    solver.add(drinks[2] == 3)

    # Clue 5: sport 3 → cigar 2 and name 2
    for i in range(4):
        solver.add(Implies(sports[i] == 3, And(cigars[i] == 2, names[i] == 2)))

    # Clue 6: water drinker (1) is in house 1 (index 0)
    solver.add(drinks[0] == 1)

    # Clue 9: cigar 0 → sport 2
    for i in range(4):
        solver.add(Implies(cigars[i] == 0, sports[i] == 2))

    if solver.check() == sat:
        model = solver.model()
        # Mappings
        name_map = {0: 'Alice', 1: 'Peter', 2: 'Arnold', 3: 'Eric'}
        cigar_map = {0: 'prince', 1: 'dunhill', 2: 'blue master', 3: 'pall mall'}
        sport_map = {0: 'swimming', 1: 'basketball', 2: 'soccer', 3: 'tennis'}
        drink_map = {0: 'coffee', 1: 'water', 2: 'milk', 3: 'tea'}

        rows = []
        for i in range(4):
            house_num = i + 1
            name_val = model[names[i]].as_long()
            cigar_val = model[cigars[i]].as_long()
            sport_val = model[sports[i]].as_long()
            drink_val = model[drinks[i]].as_long()
            rows.append([
                str(house_num),
                name_map[name_val],
                cigar_map[cigar_val],
                sport_map[sport_val],
                drink_map[drink_val]
            ])

        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                "rows": rows
            }
        }

        print(json.dumps(solution))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()