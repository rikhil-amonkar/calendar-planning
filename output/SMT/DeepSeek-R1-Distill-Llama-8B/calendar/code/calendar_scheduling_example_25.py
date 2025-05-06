from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define Anthony's available intervals
    anthony_available = [
        (0, 60),
        (70, 120),
        (180, 300),
        (330, 480)
    ]

    # Define Pamela's available intervals
    pamela_available = [
        (0, 60),
        (70, 390)
    ]

    # Define Zachary's available intervals
    zachary_available = [
        (480, 720),
        (750, 780),
        (810, 870)
    ]

    # Add constraints for Anthony
    for (a_start, a_end) in anthony_available:
        model.add_constraint(t >= a_start)
        model.add_constraint(t <= a_end)

    # Add constraints for Pamela
    for (p_start, p_end) in pamela_available:
        model.add_constraint(t >= p_start)
        model.add_constraint(t <= p_end)

    # Add constraints for Zachary
    for (z_start, z_end) in zachary_available:
        model.add_constraint(t >= z_start)
        model.add_constraint(t <= z_end)

    # Pamela's constraint: t <= 14:30 (330 minutes)
    model.add_constraint(t <= 330)

    # Solve the problem
    result = model.solve()
    if result:
        print("Possible solution: t =", result[t].numerator())
        print("Convert t to time:", time(t))
    else:
        print("No solution.")

def time(t):
    # Convert minutes back to hours:minutes
    hours = t // 60
    minutes = t % 60
    return f"{hours:02d}:{minutes:02d}"

if __name__ == "__main__":
    main()