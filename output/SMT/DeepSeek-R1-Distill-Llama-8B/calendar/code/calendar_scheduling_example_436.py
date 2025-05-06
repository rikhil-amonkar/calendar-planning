from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Patrick's blocked intervals
        (1500, 1530), (1740, 1765),
        # Shirley's blocked intervals
        (0, 30), (330, 390), (690, 750), (1050, 1080), (1500, 1530), (1800, 1980),
        # Jeffrey's blocked intervals
        (0, 30), (210, 240), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980),
        # Gloria's blocked intervals
        (780, 810), (1380, 1410),
        # Nathan's blocked intervals
        (0, 30), (210, 240), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980),
        # Angela's blocked intervals
        (0, 30), (150, 180), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980),
        # David's blocked intervals
        (0, 30), (150, 180), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980)
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