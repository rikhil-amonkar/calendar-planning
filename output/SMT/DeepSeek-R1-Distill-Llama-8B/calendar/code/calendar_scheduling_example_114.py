from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Stephanie's blocked intervals
        (600, 660), (2400, 2460),
        # Cheryl's blocked intervals
        (600, 660), (690, 750), (1170, 1200), (1500, 1530), (2010, 2040), (2400, 2460),
        # Bradley's blocked intervals
        (150, 180), (690, 750), (1170, 1200), (1500, 1530), (1950, 1980), (2100, 2130), (2340, 2400),
        # Steven's blocked intervals
        (0, 420), (780, 810), (1500, 1530), (1950, 1980), (2340, 2400)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

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