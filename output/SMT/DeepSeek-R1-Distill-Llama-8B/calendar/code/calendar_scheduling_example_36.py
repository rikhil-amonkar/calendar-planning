from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Ryan's blocked intervals
        (0, 30), (1500, 1530),
        # Ruth is available the entire day
        (0, 480),
        # Denise's blocked intervals
        (150, 180), (300, 330), (600, 660), (840, 870), (1950, 1980), (2100, 2400)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Denise's constraint: t <= 12:30 (750 minutes)
    model.add_constraint(t <= 750)

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