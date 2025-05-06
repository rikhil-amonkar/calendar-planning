from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Christine's blocked intervals
        (150, 180), (690, 750), (1170, 1260), (1500, 1530), (2010, 2040), (2340, 2400),
        # Janice is available the entire day
        (0, 480),
        # Bobby's blocked intervals
        (780, 810), (1950, 1980),
        # Elizabeth's blocked intervals
        (0, 30), (690, 750), (1170, 1260), (1500, 1500), (1800, 1980),
        # Tyler's blocked intervals
        (0, 90), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980),
        # Edward's blocked intervals
        (0, 30), (150, 180), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Janice's constraint: t <= 13:00 (780 minutes)
    model.add_constraint(t <= 780)

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