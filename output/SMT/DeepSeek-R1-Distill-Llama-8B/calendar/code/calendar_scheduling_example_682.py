from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Amanda's blocked intervals
        (150, 180), (330, 390), (690, 750), (1170, 1260), (1500, 1530), (1800, 1980),
        # Nathan's blocked intervals
        (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980),
        (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980),
        (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980),
        (300, 330), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Amanda's constraint: t <= 11:00 (330 minutes)
    model.add_constraint(t <= 330)

    # Nathan's constraint: day != 0 (Monday)
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