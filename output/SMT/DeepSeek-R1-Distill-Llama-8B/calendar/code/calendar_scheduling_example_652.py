from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Jesse's blocked intervals
        # Monday
        (1170, 1170), (1710, 1740), (1950, 1980),
        # Tuesday
        (0, 30), (780, 810), (1500, 1530),
        # Lawrence's blocked intervals
        # Monday
        (0, 3900),
        # Tuesday
        (150, 180), (330, 390), (750, 780), (1050, 1170), (1500, 1530), (1800, 1950), (2100, 2400)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Lawrence's constraint: if day is Tuesday, t <= 16:30 (2010 minutes)
    model.add_constraint((day == 1) >> (t <= 2010))

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