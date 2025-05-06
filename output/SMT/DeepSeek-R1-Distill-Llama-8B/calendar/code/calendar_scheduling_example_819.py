from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Julie has no meetings the whole week
        (0, 480),
        # Ruth's blocked intervals
        # Monday
        (0, 3900),
        # Tuesday
        (0, 3900),
        # Wednesday
        (0, 3900),
        # Thursday
        (0, 60), (210, 330), (330, 420), (690, 1050), (1260, 1500), (1680, 1800), (2100, 2400)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Julie's constraint: if day is Thursday, t >= 11:30 (690 minutes)
    model.add_constraint((day == 3) >> (t >= 690))

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