import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]  # indices 0..4 correspond to houses 1..5

    names = ['Peter', 'Alice', 'Eric', 'Bob', 'Arnold']
    birthdays = ['april', 'feb', 'mar', 'jan', 'sept']
    cigars = ['pall mall', 'prince', 'dunhill', 'blends', 'blue master']
    drinks = ['water', 'coffee', 'tea', 'milk', 'root beer']

    solutions = []

    for name_pos in itertools.permutations(names):
        # 13. Eric is in the third house.
        if name_pos[2] != 'Eric':
            continue

        eric_i = 2
        peter_i = name_pos.index('Peter')
        arnold_i = name_pos.index('Arnold')

        # 9. Arnold is directly left of Peter.
        if arnold_i != peter_i - 1:
            continue

        # 5. Peter is somewhere to the right of the root beer lover (Eric).
        if peter_i <= eric_i:
            continue

        bob_i = name_pos.index('Bob')

        for bday_pos in itertools.permutations(birthdays):
            # 8. The person whose birthday is in February is in the second house.
            if bday_pos[1] != 'feb':
                continue

            # 3. The person whose birthday is in April is Bob.
            if bday_pos.index('april') != bob_i:
                continue

            # 6. There is one house between the person whose birthday is in January and Peter.
            if abs(bday_pos.index('jan') - peter_i) != 2:
                continue

            for cigar_pos in itertools.permutations(cigars):
                # 2. Pall Mall is in the third house.
                if cigar_pos[2] != 'pall mall':
                    continue

                # 7. The person who smokes blends is the person whose birthday is in February.
                if cigar_pos[bday_pos.index('feb')] != 'blends':
                    continue

                # 4. Dunhill smoker has birthday in March.
                if cigar_pos[bday_pos.index('mar')] != 'dunhill':
                    continue

                for drink_pos in itertools.permutations(drinks):
                    # 1. The root beer lover is Eric.
                    if drink_pos[eric_i] != 'root beer':
                        continue

                    # 10. The person who likes milk is not in the fifth house.
                    if drink_pos[4] == 'milk':
                        continue

                    # 11. Blue Master smoker is the coffee drinker. (bidirectional)
                    coffee_i = drink_pos.index('coffee')
                    if cigar_pos[coffee_i] != 'blue master':
                        continue
                    if drink_pos[cigar_pos.index('blue master')] != 'coffee':
                        continue

                    # 12. One house between tea and coffee.
                    if abs(drink_pos.index('tea') - coffee_i) != 2:
                        continue

                    # All constraints satisfied; build solution
                    sol_rows = []
                    for h in range(5):
                        sol_rows.append([
                            str(houses[h]),
                            name_pos[h],
                            bday_pos[h],
                            cigar_pos[h],
                            drink_pos[h]
                        ])
                    solutions.append(sol_rows)

    if not solutions:
        raise RuntimeError("No solution found.")
    # Assuming unique solution; take the first
    rows = solutions[0]
    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result))