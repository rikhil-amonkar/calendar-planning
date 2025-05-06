from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Kimberly's blocked intervals
        (600, 660), (780, 840), (2880, 3060),
        # Megan is available the entire day
        (0, 480),
        # Marie's blocked intervals
        (600, 660), (750, 1050), (1800, 1950), (1950, 1980), (1980, 2010), (2010, 2040), (2040, 2100), (2100, 2160), (2160, 2400), (2400, 2400),
        # Diana's blocked intervals
        (150, 180), (690, 1050), (1950, 2070), (2070, 2100), (2100, 2400)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Megan's constraint: t >= 10:00 (600 minutes)
    model.add_constraint(t >= 600)

    # Solve the problem
    result = model.solve()
    if result:
        print("Possible solution: t =", result[t].numerator())
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