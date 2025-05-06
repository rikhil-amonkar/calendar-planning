from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday, 4 for Friday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Betty's blocked days: Wednesday (2) and Thursday (3)
        (0, 480),  # Monday
        (0, 480),  # Tuesday
        (0, 480),  # Friday
        # Megan's blocked intervals on each day
        # Monday
        (0, 3900),  # Blocked the entire day
        # Tuesday
        (0, 3900),  # Blocked the entire day
        # Wednesday
        (0, 3900),  # Blocked the entire day
        # Thursday
        (0, 3900),  # Blocked the entire day
        # Friday
        (0, 3900),  # Blocked the entire day
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Betty's constraints: day cannot be Wednesday (2) or Thursday (3)
    model.add_constraint(day != 2)
    model.add_constraint(day != 3)

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