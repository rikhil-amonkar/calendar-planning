from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday, 4 for Friday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Bryan's blocked intervals
        (210, 240), (690, 750), (1500, 1530), (1740, 1765),
        # Nicholas's blocked intervals
        (660, 690), (780, 810), (1050, 1080), (1500, 1530), (1800, 1950),
        (660, 690), (780, 810), (1050, 1080), (1500, 1500), (1800, 1950),
        (660, 690), (780, 810), (1050, 1080), (1500, 1500), (1800, 1950),
        (660, 690), (780, 810), (1050, 1080), (1500, 1500), (1800, 1950),
        (660, 690), (780, 810), (1050, 1080), (1500, 1500), (1800, 1950),
        (660, 690), (780, 810), (1050, 1080), (1500, 1500), (1800, 1950),
        (660, 690), (780, 810), (1050, 1080), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Bryan's constraint: day != 1 (Tuesday)
    model.add_constraint(day != 1)

    # Nicholas's constraints: day cannot be Monday (0), Thursday (3)
    model.add_constraint((day == 0) >> (t <= 2400))
    model.add_constraint((day == 3) >> (t <= 2400))

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