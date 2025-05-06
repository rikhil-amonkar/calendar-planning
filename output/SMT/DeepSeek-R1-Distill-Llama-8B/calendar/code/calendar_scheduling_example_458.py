from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Wayne is available the entire day
        (0, 480),
        # Melissa's blocked intervals
        (600, 660), (1170, 1320), (1800, 1830),
        # Catherine is available the entire day
        (0, 480),
        # Gregory's blocked intervals
        (1170, 1200), (1950, 1980),
        # Victoria's blocked intervals
        (0, 30), (210, 240), (690, 750), (1260, 1380), (1500, 1530), (1800, 1950), (2100, 2400),
        # Thomas's blocked intervals
        (600, 780), (1170, 1200), (1950, 2100),
        # Jennifer's blocked intervals
        (0, 30), (210, 240), (450, 570), (690, 750), (1050, 1170), (1500, 1530), (1800, 1950), (2100, 2400)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Wayne's constraint: t >= 14:00 (840 minutes)
    model.add_constraint(t >= 840)

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