from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # John's blocked intervals on day 0 (Monday), day 1 (Tuesday), day 2 (Wednesday) after 14:30 (2100 minutes)
        # Monday
        (0, 480),
        # Tuesday
        (0, 480),
        # Wednesday
        (0, 480),
        # Jennifer's blocked intervals
        # Monday
        (0, 330), (690, 750), (1050, 1080), (1500, 1530), (1800, 1980),
        # Tuesday
        (0, 330), (690, 750), (1050, 1080), (1500, 1530), (1800, 1980),
        # Wednesday
        (0, 330), (690, 750), (1050, 1080), (1500, 1530), (1800, 1980)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # John's constraints: day cannot be Monday, Tuesday, or Wednesday after 14:30 (2100 minutes)
    model.add_constraint((day == 0) >> (t >= 2100))
    model.add_constraint((day == 1) >> (t >= 2100))
    model.add_constraint((day == 2) >> (t >= 2100))

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