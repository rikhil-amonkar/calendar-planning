from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Emily's blocked intervals
        (600, 660), (690, 750), (1380, 1410), (1740, 1765),
        # Melissa's blocked intervals
        (150, 180), (1740, 1765),
        # Frank's blocked intervals
        (0, 30), (210, 240), (330, 390), (690, 750), (1050, 1080), (1500, 1500), (1800, 1980)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Frank's constraint: t <= 9:30 (150 minutes)
    model.add_constraint(t <= 150)

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