from z3 import *

def main():
    t = Variable('t')  # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Gregory's blocked intervals
        (0, 60), (210, 240), (330, 360), (480, 540),
        # Natalie is available the entire day
        (0, 480),
        # Christine's blocked intervals
        (0, 690), (2700, 3900),
        # Vincent's blocked intervals
        (0, 30), (210, 300), (360, 480), (690, 1050), (1050, 1320), (1320, 1500), (1500, 1800)
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