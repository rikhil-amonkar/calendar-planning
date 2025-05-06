from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Russell's blocked intervals
        (690, 750), (1950, 1980),
        # Alexander's blocked intervals
        # Monday
        (0, 690), (750, 1050), (1500, 1800),
        # Tuesday
        (0, 30), (780, 810), (1500, 1530), (1800, 2010), (2100, 2400)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Russell's constraint: if day is Tuesday, t >= 13:30 (2010 minutes)
    model.add_constraint((day == 1) >> (t >= 2010))

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