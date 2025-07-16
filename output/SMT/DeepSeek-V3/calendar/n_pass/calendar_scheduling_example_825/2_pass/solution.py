from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Possible days: 0 (Monday), 1 (Tuesday), 3 (Thursday). Wednesday (2) is excluded.
    day = Int('day')
    s.add(Or(day == 0, day == 1, day == 3))

    # Start time in minutes from 9:00 (540 minutes from midnight)
    start_time = Int('start_time')
    # Meeting duration is 60 minutes (1 hour)
    duration = 60
    end_time = start_time + duration

    # Working hours: 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540)
    s.add(end_time <= 1020)

    # Laura's busy times per day in minutes from midnight
    laura_busy = {
        0: [(10*60 + 30, 11*60), (12*60 + 30, 13*60), (14*60 + 30, 15*60 + 30), (16*60, 17*60)],
        1: [(9*60 + 30, 10*60), (11*60, 11*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60), (16*60, 17*60)],
        2: [(11*60 + 30, 12*60), (12*60 + 30, 13*60), (15*60 + 30, 16*60 + 30)],
        3: [(10*60 + 30, 11*60), (12*60, 13*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
    }

    # Philip's busy times per day in minutes from midnight
    philip_busy = {
        0: [(9*60, 17*60)],  # All day busy on Monday
        1: [(9*60, 11*60), (11*60 + 30, 12*60), (13*60, 13*60 + 30), (14*60, 14*60 + 30), (15*60, 16*60 + 30)],
        2: [(9*60, 10*60), (11*60, 12*60), (12*60 + 30, 16*60), (16*60 + 30, 17*60)],
        3: [(9*60, 10*60 + 30), (11*60, 12*60 + 30), (13*60, 17*60)]
    }

    # Constraints for each possible day
    def add_day_constraints(d):
        # Laura's constraints for day d
        laura_no_overlap = []
        for (busy_start, busy_end) in laura_busy[d]:
            laura_no_overlap.append(Or(end_time <= busy_start, start_time >= busy_end))
        # All Laura's busy times must be non-overlapping
        s.add(Implies(day == d, And(laura_no_overlap)))

        # Philip's constraints for day d
        philip_no_overlap = []
        for (busy_start, busy_end) in philip_busy[d]:
            philip_no_overlap.append(Or(end_time <= busy_start, start_time >= busy_end))
        # All Philip's busy times must be non-overlapping
        s.add(Implies(day == d, And(philip_no_overlap)))

    # Add constraints for each day
    add_day_constraints(0)  # Monday
    add_day_constraints(1)  # Tuesday
    add_day_constraints(3)  # Thursday

    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        start = m[start_time].as_long()
        end = start + duration

        # Convert day number to day name
        day_names = {0: "Monday", 1: "Tuesday", 3: "Thursday"}
        day_str = day_names[d]

        # Convert start and end times to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        start_str = minutes_to_time(start)
        end_str = minutes_to_time(end)

        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()