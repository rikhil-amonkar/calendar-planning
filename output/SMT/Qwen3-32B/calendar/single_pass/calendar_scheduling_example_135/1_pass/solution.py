from z3 import *

def main():
    solver = Solver()

    S = Int('S')

    # Work hours from 9:00 (540) to 17:00 (620), meeting is 30 min
    solver.add(S >= 540)
    solver.add(S + 30 <= 620)  # Ensures the meeting ends by 17:00

    # Ashley's busy times (in minutes since midnight)
    ashley_buses = [
        (600, 630),  # 10:00-10:30
        (660, 720),  # 11:00-12:00
        (750, 780),  # 12:30-13:00
        (900, 960),  # 15:00-16:00
    ]
    for start, end in ashley_buses:
        solver.add(Or(S + 30 <= start, S >= end))

    # Ronald's busy times
    ronald_buses = [
        (540, 570),  # 9:00-9:30
        (600, 690),  # 10:00-11:30
        (750, 840),  # 12:30-14:00
        (870, 1020), # 14:30-17:00
    ]
    for start, end in ronald_buses:
        solver.add(Or(S + 30 <= start, S >= end))

    # Larry's busy times
    larry_buses = [
        (540, 720),  # 9:00-12:00
        (780, 1020), # 13:00-17:00
    ]
    for start, end in larry_buses:
        solver.add(Or(S + 30 <= start, S >= end))

    # Eric has no busy times, so no constraints are needed.

    if solver.check() == sat:
        model = solver.model()
        s_val = model[S].as_long()
        start_time = s_val
        end_time = s_val + 30
        # Convert minutes to HH:MM format
        def to_time(mins):
            h = mins // 60
            m = mins % 60
            return f"{h:02d}:{m:02d}"
        day = "Monday"
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {to_time(start_time)}")
        print(f"End Time: {to_time(end_time)}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()