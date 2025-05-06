from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Robert's blocked intervals
        # Monday
        (690, 750), (1680, 1710), (2340, 2370),
        # Tuesday
        (690, 750), (2250, 2280),
        # Wednesday
        (570, 600), (690, 750), (1170, 1200), (1500, 1530), (1800, 1950), (2100, 2130), (2340, 2370),
        # Ralph's blocked intervals
        # Monday
        (600, 1380), (1500, 1980),
        # Tuesday
        (0, 30), (300, 330), (600, 630), (900, 1050), (1200, 1350), (1500, 1650), (1800, 1950),
        # Wednesday
        (600, 630), (750, 780), (1500, 1530), (1800, 1950), (2100, 2130), (2340, 2370)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Robert's constraint: day != 0 (Monday)
    model.add_constraint(day != 0)

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