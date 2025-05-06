from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Mary's blocked intervals
        (0, 30), (600, 660), (1500, 1530), (1800, 1950),
        (300, 330), (750, 780), (1950, 1980),
        # Alexis's blocked intervals
        # Monday
        (0, 30), (210, 240), (330, 420), (690, 750), (840, 900), (1170, 1380), (1500, 1500), (1800, 1950),
        # Tuesday
        (0, 30), (210, 240), (300, 330), (690, 750), (840, 900), (1170, 1380), (1500, 1500), (1800, 1950),
        # Wednesday
        (0, 30), (210, 240), (300, 330), (690, 750), (840, 900), (1170, 1380), (1500, 1500), (1800, 1950),
        # Thursday
        (0, 30), (210, 240), (300, 330), (690, 750), (840, 900), (1170, 1380), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

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