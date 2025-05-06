from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Margaret's blocked intervals
        # Monday
        (690, 750), (1170, 1200), (1950, 1980), (2340, 2400),
        # Tuesday
        (1320, 1350),
        # Alexis's blocked intervals
        # Monday
        (150, 210), (690, 750), (1170, 1200), (1500, 1800),
        # Tuesday
        (0, 30), (300, 330), (1500, 1530), (1800, 2010)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Margaret's constraints: day cannot be Monday (0) or t < 14:30 (2100 minutes) on Tuesday
    model.add_constraint(day != 0)
    model.add_constraint((day == 1) >> (t >= 2100))

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