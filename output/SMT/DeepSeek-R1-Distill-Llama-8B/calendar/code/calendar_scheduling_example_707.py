from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Ryan's blocked intervals
        # Monday
        (150, 180), (660, 690), (780, 810), (1050, 1080), (1500, 1530), (1950, 1980),
        # Tuesday
        (690, 750), (1500, 1530), (1950, 1980),
        # Wednesday
        (780, 810), (1500, 1530), (2010, 2100), (2340, 2400),
        # Adam's blocked intervals
        # Monday
        (0, 90), (150, 180), (300, 330), (750, 780), (1050, 1080), (1500, 1500), (1800, 1980),
        # Tuesday
        (0, 30), (150, 180), (300, 330), (750, 780), (1050, 1080), (1500, 1500), (1800, 1950),
        # Wednesday
        (0, 30), (150, 180), (300, 330), (750, 780), (1050, 1080), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Ryan's constraint: day != 2 (Wednesday)
    model.add_constraint(day != 2)

    # Adam's constraints: day cannot be Monday before 14:30 (1500 minutes), Tuesday, or Wednesday
    model.add_constraint(day != 0)
    model.add_constraint(day != 1)
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