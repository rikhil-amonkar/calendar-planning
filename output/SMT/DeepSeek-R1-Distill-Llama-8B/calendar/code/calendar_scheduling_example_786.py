from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Amy's busy intervals on Wednesday
        (690, 750), (2550, 2700),
        # Pamela's busy intervals
        # Monday
        (0, 690), (750, 4800),
        # Tuesday
        (90, 210), (300, 3900),
        # Wednesday
        (90, 300), (750, 1050), (1950, 2100), (2400, 2700), (3000, 3300)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Pamela's additional constraints
    # Avoid Monday
    model.add_constraint(day != 0)
    # Avoid Tuesday before 16:00 (900 minutes)
    model.add_constraint((day == 1) >> (t >= 900))
    # Avoid Wednesday before 16:00 (900 minutes)
    model.add_constraint((day == 2) >> (t >= 900))

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