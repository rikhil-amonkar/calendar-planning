from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Jean's blocked intervals
        (780, 810), (2010, 2040),
        # Doris's blocked intervals
        (0, 330), (690, 750), (1050, 1080), (1500, 1530), (1800, 1980),
        # Available time for both
        (0, 480)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Doris's constraint: if day is Monday, t <= 14:00 (1500 minutes)
    model.add_constraint((day == 0) >> (t <= 1500))

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