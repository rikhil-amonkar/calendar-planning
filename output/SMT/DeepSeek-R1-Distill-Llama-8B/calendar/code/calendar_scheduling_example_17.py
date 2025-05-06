from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Margaret's blocked intervals
        (0, 30), (210, 240), (330, 360), (780, 810), (1500, 1500),
        # Donna's blocked intervals
        (2100, 2160), (2400, 2430),
        # Helen's blocked intervals
        (0, 30), (150, 180), (300, 330), (420, 450), (750, 780), (1050, 1080), (1500, 1500), (1800, 1980)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Helen's constraint: t <= 13:30 (780 minutes)
    model.add_constraint(t <= 780)

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