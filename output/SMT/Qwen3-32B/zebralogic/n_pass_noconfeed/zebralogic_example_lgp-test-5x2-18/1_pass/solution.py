import json
from z3 import *

def main():
    # Define variables for each person's house and each child's house
    E_house = Int('E_house')  # Eric
    A_house = Int('A_house')  # Alice
    P_house = Int('P_house')  # Peter
    B_house = Int('B_house')  # Bob
    Ar_house = Int('Ar_house')  # Arnold

    T_house = Int('T_house')  # Timothy
    M_house = Int('M_house')  # Meredith
    S_house = Int('S_house')  # Samantha
    F_house = Int('F_house')  # Fred
    Be_house = Int('Be_house')  # Bella

    solver = Solver()

    # Constraints for name houses: 1-5, distinct
    solver.add(And(1 <= E_house, E_house <= 5))
    solver.add(And(1 <= A_house, A_house <= 5))
    solver.add(And(1 <= P_house, P_house <= 5))
    solver.add(And(1 <= B_house, B_house <= 5))
    solver.add(And(1 <= Ar_house, Ar_house <= 5))
    solver.add(Distinct(E_house, A_house, P_house, B_house, Ar_house))

    # Constraints for child houses: 1-5, distinct
    solver.add(And(1 <= T_house, T_house <= 5))
    solver.add(And(1 <= M_house, M_house <= 5))
    solver.add(And(1 <= S_house, S_house <= 5))
    solver.add(And(1 <= F_house, F_house <= 5))
    solver.add(And(1 <= Be_house, Be_house <= 5))
    solver.add(Distinct(T_house, M_house, S_house, F_house, Be_house))

    # Linking constraints: each child's house is the same as a name's house
    for child_var in [T_house, M_house, S_house, F_house, Be_house]:
        solver.add(Or(
            child_var == E_house,
            child_var == A_house,
            child_var == P_house,
            child_var == B_house,
            child_var == Ar_house
        ))

    # Clue 3: Fred is in second house
    solver.add(F_house == 2)

    # Clue 7: Fred directly left of Bella => F_house + 1 == Be_house
    solver.add(Be_house == F_house + 1)

    # Clue 1: Bob is left of Samantha's house
    solver.add(B_house < S_house)

    # Clue 2: Mother of Timothy is left of Samantha's house => T_house < S_house
    solver.add(T_house < S_house)

    # Clue 4: One house between Alice and Samantha => |A_house - S_house| == 2
    solver.add(Or(
        A_house - S_house == 2,
        S_house - A_house == 2
    ))

    # Clue 5: Eric not in third house
    solver.add(E_house != 3)

    # Clue 6: Bob not in third house
    solver.add(B_house != 3)

    # Clue 8: Samantha's house is left of Peter's
    solver.add(S_house < P_house)

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()

        # Prepare the solution data
        names_list = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
        children_list = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']

        rows = []
        for house_num in range(1, 6):
            # Determine the name for this house
            name = None
            for idx, var in enumerate([E_house, A_house, P_house, B_house, Ar_house]):
                if model.eval(var).as_long() == house_num:
                    name = names_list[idx]
                    break

            # Determine the child for this house
            child = None
            for idx, var in enumerate([T_house, M_house, S_house, F_house, Be_house]):
                if model.eval(var).as_long() == house_num:
                    child = children_list[idx]
                    break

            rows.append([str(house_num), name, child])

        # Build the JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": rows
            }
        }

        # Print the JSON output
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()