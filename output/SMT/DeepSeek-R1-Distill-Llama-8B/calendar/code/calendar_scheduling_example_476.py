from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Daniel is available the entire day
        (0, 480),
        # Kathleen's blocked interval
        (2700, 2850),
        # Carolyn's blocked intervals
        (780, 810), (1170, 1200),
        # Roger is available the entire day
        (0, 480),
        # Cheryl's blocked intervals
        (0, 30), (210, 330), (690, 750), (1500, 1800),
        # Virginia's blocked intervals
        (150, 210), (330, 420), (690, 750), (1950, 2100), (2400, 2700),
        # Angela's blocked intervals
        (150, 180), (330, 420), (690, 750), (1050, 1170), (1500, 1800)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Roger's constraint: t >= 12:30 (750 minutes)
    model.add_constraint(t >= 750)

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