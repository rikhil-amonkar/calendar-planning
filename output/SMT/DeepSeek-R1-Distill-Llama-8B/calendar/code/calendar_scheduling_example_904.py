from z3 import *

def main():
    day = Variable('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday, 4 for Friday
    t = Variable('t')      # start time in minutes from 9:00

    # Define available intervals for each person
    available = [
        # Daniel's blocked intervals
        (150, 180), (690, 750), (1170, 1260), (1500, 1530), (1800, 1980), (2100, 2130),
        (300, 330), (750, 780), (1050, 1080), (1500, 1500), (1800, 1980), (2100, 2130),
        (300, 330), (750, 780), (1050, 1080), (1500, 1500), (1800, 1980), (2100, 2130),
        (300, 330), (750, 780), (1050, 1080), (1500, 1500), (1800, 1980), (2100, 2130),
        (300, 330), (750, 780), (1050, 1080), (1500, 1500), (1800, 1980), (2100, 2130),
        # Bradley's blocked intervals
        (150, 180), (330, 390), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950),
        (150, 180), (330, 390), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950),
        (150, 180), (330, 390), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950),
        (150, 180), (330, 390), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950),
        (150, 180), (330, 390), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950),
        (150, 180), (330, 390), (690, 750), (1050, 1080), (1500, 1500), (1800, 1950)
    ]

    # Create constraints for each available interval
    for interval in available:
        model.add_constraint(t >= interval[0])
        model.add_constraint(t <= interval[1])

    # Daniel's constraints: day cannot be Wednesday (2), Thursday (3), or Friday (4)
    model.add_constraint(day != 2)
    model.add_constraint(day != 3)
    model.add_constraint(day != 4)

    # Bradley's constraints: day cannot be Monday before 11:00 (330 minutes)
    model.add_constraint((day == 0) >> (t >= 330))

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