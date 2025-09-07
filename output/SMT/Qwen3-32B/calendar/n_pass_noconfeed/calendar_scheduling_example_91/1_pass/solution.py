from z3 import *

def main():
    solver = Solver()

    start_time = Int('start_time')

    # Work hours constraints (9:00 to 17:00 is 540 to 1020, but meeting can start up to 960)
    solver.add(start_time >= 540)
    solver.add(start_time <= 960)

    # Define busy intervals for each participant
    danielle_intervals = [
        (540, 600),  # 9:00-10:00
        (630, 660),  # 10:30-11:00
        (870, 900),  # 14:30-15:00
        (930, 960),  # 15:30-16:00
        (990, 1020)  # 16:30-17:00
    ]

    bruce_intervals = [
        (660, 690),   # 11:00-11:30
        (750, 780),   # 12:30-13:00
        (840, 870),   # 14:00-14:30
        (930, 960)    # 15:30-16:00
    ]

    eric_intervals = [
        (540, 570),   # 9:00-9:30
        (600, 660),   # 10:00-11:00
        (690, 780),   # 11:30-13:00
        (870, 930)    # 14:30-15:30
    ]

    # Add constraints for each interval
    for s, e in danielle_intervals + bruce_intervals + eric_intervals:
        solver.add(Or(start_time + 60 <= s, start_time >= e))

    if solver.check() == sat:
        model = solver.model()
        start = model[start_time].as_long()
        end = start + 60
        day = "Monday"
        print(f"{to_time(start)}:{to_time(end)} {day}")
    else:
        print("No solution found.")

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

if __name__ == "__main__":
    main()