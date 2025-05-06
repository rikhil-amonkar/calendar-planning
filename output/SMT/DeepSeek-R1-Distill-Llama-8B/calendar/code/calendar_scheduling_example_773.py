from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Patrick is available the entire week
        (0, 480),
        # Roy's blocked intervals
        # Monday
        (330, 390), (600, 660), (780, 810), (1050, 1080), (1500, 1530), (1800, 1980),
        # Tuesday
        (150, 180), (330, 390), (600, 660), (750, 780), (1050, 1080), (1500, 1500), (1800, 1950),
        # Wednesday
        (150, 180), (330, 390), (600, 660), (750, 780), (1050, 1080), (1500, 1500), (1800, 1950)
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