from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the variables
    day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
    start_time = Int('start_time')  # in minutes from 00:00 (e.g., 9:00 is 540)

    # Constraints for day: must be 0, 1, or 2 (Mon, Tue, Wed)
    s.add(day >= 0, day <= 2)

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540, start_time + 60 <= 1020)

    # Stephanie's existing meetings
    stephanie_meetings = {
        0: [(570, 600), (630, 660), (690, 720), (840, 870)],  # Monday
        1: [(720, 780)],  # Tuesday
        2: [(540, 600), (780, 840)]  # Wednesday
    }

    # Betty's existing meetings
    betty_meetings = {
        0: [(540, 600), (660, 690), (870, 900), (930, 960)],  # Monday
        1: [(540, 570), (690, 720), (750, 870), (930, 960)],  # Tuesday
        2: [(600, 690), (720, 840), (870, 1020)]  # Wednesday
    }

    # Function to add no-overlap constraints for a person's meetings on a given day
    def add_no_overlap_constraints(day_var, start, person_meetings):
        for d in person_meetings:
            for (meeting_start, meeting_end) in person_meetings[d]:
                # If the meeting is on day d, then the new meeting must not overlap
                s.add(Not(And(day_var == d,
                              Or(And(start >= meeting_start, start < meeting_end),
                                 And(start + 60 > meeting_start, start + 60 <= meeting_end),
                                 And(start <= meeting_start, start + 60 >= meeting_end)))))

    # Add no-overlap constraints for Stephanie and Betty
    add_no_overlap_constraints(day, start_time, stephanie_meetings)
    add_no_overlap_constraints(day, start_time, betty_meetings)

    # Stephanie prefers to avoid Monday (day 0)
    s.add(day != 0)

    # Betty cannot meet on Tuesday after 12:30 (750 minutes) if day is Tuesday
    s.add(Not(And(day == 1, start_time >= 750)))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()

        # Convert day_val to day string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]

        # Convert start and end times to HH:MM format
        start_hh = start_val // 60
        start_mm = start_val % 60
        end_val = start_val + 60
        end_hh = end_val // 60
        end_mm = end_val % 60

        # Format the times with leading zeros
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()