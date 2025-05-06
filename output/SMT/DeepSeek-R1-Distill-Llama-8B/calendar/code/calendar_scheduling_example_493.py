from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Tyler is available the entire day
        (0, 480),
        # Kelly is available the entire day
        (0, 480),
        # Stephanie's blocked intervals
        (690, 750), (2700, 3000), (2790, 2850),
        # Hannah is available the entire day
        (0, 480),
        # Joe's blocked intervals
        (540, 900), (630, 1200), (690, 1050), (840, 3900),
        # Diana's blocked intervals
        (540, 690), (750, 780), (870, 1050), (2790, 2850), (3000, 3600),
        # Deborah's blocked intervals
        (540, 600), (690, 1200), (750, 780), (870, 900), (2790, 2850), (3000, 3300)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

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