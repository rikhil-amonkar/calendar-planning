from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Possible days: 0 (Monday), 1 (Tuesday), 2 (Wednesday), 3 (Thursday). But Philip can't meet on Wednesday.
    day = Int('day')
    s.add(Or(day == 0, day == 1, day == 3))  # Wednesday (2) is excluded

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
    # For each day, the meeting should not overlap with any busy times of Laura or Philip on that day
    def add_day_constraints(d):
        # Laura's constraints for day d
        laura_no_overlap = []
        for (busy_start, busy_end) in laura_busy[d]:
            laura_no_overlap.append(Or(end_time <= busy_start, start_time >= busy_end))
        # All Laura's busy times must be non-overlapping
        s.add(And(laura_no_overlap))

        # Philip's constraints for day d
        philip_no_overlap = []
        for (busy_start, busy_end) in philip_busy[d]:
            philip_no_overlap.append(Or(end_time <= busy_start, start_time >= busy_end))
        # All Philip's busy times must be non-overlapping
        s.add(And(philip_no_overlap))

    # Add constraints based on the selected day
    day_constraints = []
    for d in [0, 1, 3]:  # Possible days: Monday (0), Tuesday (1), Thursday (3)
        # If day is d, then add the corresponding constraints
        cond = (day == d)
        # Create temporary solver to check if day d is feasible
        temp_s = Solver()
        temp_s.add(start_time >= 540)
        temp_s.add(end_time <= 1020)
        # Laura's constraints for day d
        laura_no_overlap = []
        for (busy_start, busy_end) in laura_busy[d]:
            laura_no_overlap.append(Or(end_time <= busy_start, start_time >= busy_end))
        temp_s.add(And(laura_no_overlap))
        # Philip's constraints for day d
        philip_no_overlap = []
        for (busy_start, busy_end) in philip_busy[d]:
            philip_no_overlap.append(Or(end_time <= busy_start, start_time >= busy_end))
        temp_s.add(And(philip_no_overlap))
        # Check if day d is feasible
        if temp_s.check() == sat:
            day_constraints.append(day == d)
    s.add(Or(day_constraints))

    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        start = m[start_time].as_long()
        end = start + duration

        # Convert day number to day name
        day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
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