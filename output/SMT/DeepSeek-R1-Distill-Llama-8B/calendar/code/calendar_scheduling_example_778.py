from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Susan's blocked intervals
        (780, 810), (1170, 1260), (1380, 1410),
        (0, 30), (210, 240),
        # Sandra's blocked intervals
        (0, 330), (690, 750), (1050, 1080), (1500, 1530), (1800, 1950),
        (0, 30), (150, 180), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950),
        (0, 30), (150, 180), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950),
        (0, 30), (150, 180), (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Susan's constraint: day != 1 (Tuesday)
    model.add_constraint(day != 1)

    # Sandra's constraints: day cannot be Monday after 16:00 (2400 minutes) or Wednesday
    model.add_constraint((day == 0) >> (t <= 2400))
    model.add_constraint((day == 2) >> (t <= 2400))

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