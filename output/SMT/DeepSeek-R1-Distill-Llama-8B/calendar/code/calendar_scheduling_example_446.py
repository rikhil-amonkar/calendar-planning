from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Megan's blocked intervals
        (0, 90), (600, 660), (780, 840),
        # Christine's blocked intervals
        (0, 90), (690, 750), (1050, 1170), (2550, 2700),
        # Gabriel is available the entire day
        (0, 480),
        # Sara's blocked intervals
        (690, 750), (2700, 2850),
        # Bruce's blocked intervals
        (150, 210), (630, 780), (750, 1050), (1950, 2100), (2400, 2700), (2850, 3000),
        # Kathryn's blocked intervals
        (600, 3300), (3600, 3900),
        # Billy's blocked intervals
        (0, 90), (660, 690), (780, 1050), (2400, 2700), (2850, 3000)
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