from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Andrea's blocked intervals
        (150, 180), (1170, 1260),
        # Ruth's blocked intervals
        (780, 810), (1500, 1530),
        # Steven's blocked intervals
        (600, 660), (690, 750), (780, 810), (1050, 1080), (1170, 1200), (1500, 1500), (1800, 1980),
        # Grace's available intervals
        (0, 480),
        # Kyle's blocked intervals
        (0, 30), (210, 240), (690, 750), (1050, 1080), (1170, 1260), (1500, 1530), (1800, 1980),
        # Elijah's blocked intervals
        (0, 90), (330, 390), (690, 750), (1170, 1260), (1500, 1500), (1800, 1980),
        # Lori's blocked intervals
        (0, 30), (300, 330), (600, 660), (780, 810), (1050, 1080), (1170, 1260), (1500, 1500), (1800, 1950)
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