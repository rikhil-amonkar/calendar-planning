from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Jose's blocked intervals
        (690, 750), (780, 810),
        # Keith's blocked intervals
        (1800, 1830), (1950, 1980),
        # Logan's blocked intervals
        (0, 30), (300, 330), (690, 750), (1500, 1530), (1800, 1980),
        # Megan's blocked intervals
        (0, 90), (210, 240), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980),
        # Gary's blocked intervals
        (0, 30), (150, 180), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950),
        # Bobby's blocked intervals
        (0, 30), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Jose's constraint: t <= 15:30 (2100 minutes)
    model.add_constraint(t <= 2100)

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