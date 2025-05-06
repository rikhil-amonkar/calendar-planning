from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Betty's blocked intervals
        # Monday
        (750, 780), (1170, 1260), (1500, 1530), (1800, 1980),
        # Tuesday
        (0, 30), (690, 750), (1170, 1260), (1500, 1530), (1800, 1980), (2100, 2400),
        # Wednesday
        (150, 180), (780, 810), (1950, 1980),
        # Thursday
        (150, 180), (690, 750), (1050, 1170), (1500, 1500), (1800, 1980),
        # Scott's blocked intervals
        # Monday
        (150, 210), (570, 1050), (1950, 2010), (2100, 2400),
        # Tuesday
        (0, 30), (210, 240), (330, 390), (750, 780), (1050, 1170), (1500, 1530), (1800, 1950),
        # Wednesday
        (150, 210), (330, 390), (750, 780), (1050, 1170), (1500, 1500), (1800, 1950),
        # Thursday
        (0, 30), (150, 180), (330, 390), (750, 780), (1050, 1170), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Betty's constraints: day cannot be Monday (0), Tuesday (1), or Thursday (3) before 15:00 (1500 minutes)
    model.add_constraint(day != 0)
    model.add_constraint((day == 1) >> (t >= 1500))
    model.add_constraint(day != 3)
    model.add_constraint((day == 3) >> (t >= 1500))

    # Scott's constraint: day cannot be Wednesday (2)
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