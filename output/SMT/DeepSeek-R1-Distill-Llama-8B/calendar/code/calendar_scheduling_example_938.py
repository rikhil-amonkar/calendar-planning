from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday, 4 for Friday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Eugene's blocked intervals
        # Monday
        (690, 750), (1170, 1200), (1500, 1530), (1800, 1830),
        # Tuesday
        (0, 480),
        # Wednesday
        (0, 30), (570, 600), (690, 750), (1170, 1200), (1500, 1500), (1800, 1980),
        # Thursday
        (150, 180), (780, 810), (1950, 1980),
        # Friday
        (690, 750), (1050, 1080), (1500, 1530),
        # Eric's blocked intervals
        # Monday
        (0, 3900),
        # Tuesday
        (0, 3900),
        # Wednesday
        (0, 330), (600, 690), (750, 780), (1050, 1170), (1500, 1500), (1800, 1950),
        # Thursday
        (0, 3900),
        # Friday
        (0, 30), (300, 330), (600, 690), (750, 780), (1050, 1170), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Eric's constraint: day != 2 (Wednesday)
    model.add_constraint(day != 2)

    # Solve the problem
    result = model.solve()
    if result:
        print("Possible solution: day =", result[day].numerator())
        print("t =", result[t].numerator())
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