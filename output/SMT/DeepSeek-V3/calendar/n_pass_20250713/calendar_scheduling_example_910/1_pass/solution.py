from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
    start_time = Int('start_time')  # in minutes from 00:00
    end_time = Int('end_time')  # in minutes from 00:00

    # Constraints for day: must be between 0 (Monday) and 4 (Friday)
    s.add(day >= 0, day <= 4)

    # Convert work hours (9:00-17:00) to minutes (540 to 1020)
    work_start = 540
    work_end = 1020

    # Meeting must be within work hours
    s.add(start_time >= work_start, end_time <= work_end)
    s.add(end_time == start_time + 60)  # Meeting duration is 1 hour

    # Bryan's preferences: avoid Tuesday (day 1)
    s.add(day != 1)

    # Nicholas's preferences: avoid Monday (day 0) and Thursday (day 3)
    s.add(day != 0, day != 3)

    # Bryan's existing meetings:
    # Thursday (3): 9:30-10:00 (570-600), 12:30-13:00 (750-780)
    # Friday (4): 10:30-11:00 (630-660), 14:00-14:30 (840-870)
    bryan_meetings = {
        3: [(570, 600), (750, 780)],
        4: [(630, 660), (840, 870)]
    }

    # Nicholas's existing meetings:
    # Monday (0): 11:30-12:00 (690-720), 13:00-15:30 (780-930)
    # Tuesday (1): 9:00-9:30 (540-570), 11:00-13:30 (660-810), 14:00-16:30 (840-990)
    # Wednesday (2): 9:00-9:30 (540-570), 10:00-11:00 (600-660), 11:30-13:30 (690-810), 14:00-14:30 (840-870), 15:00-16:30 (900-990)
    # Thursday (3): 10:30-11:30 (630-690), 12:00-12:30 (720-750), 15:00-15:30 (900-930), 16:30-17:00 (990-1020)
    # Friday (4): 9:00-10:30 (540-630), 11:00-12:00 (660-720), 12:30-14:30 (750-870), 15:30-16:00 (930-960), 16:30-17:00 (990-1020)
    nicholas_meetings = {
        0: [(690, 720), (780, 930)],
        1: [(540, 570), (660, 810), (840, 990)],
        2: [(540, 570), (600, 660), (690, 810), (840, 870), (900, 990)],
        3: [(630, 690), (720, 750), (900, 930), (990, 1020)],
        4: [(540, 630), (660, 720), (750, 870), (930, 960), (990, 1020)]
    }

    # Function to add no-overlap constraints for a participant's meetings on the selected day
    def add_no_overlap_constraints(participant_meetings, day_var, start, end):
        for d, meetings in participant_meetings.items():
            for meeting_start, meeting_end in meetings:
                s.add(Not(And(day_var == d,
                              Or(And(start >= meeting_start, start < meeting_end),
                                 And(end > meeting_start, end <= meeting_end),
                                 And(start <= meeting_start, end >= meeting_end))))

    # Add no-overlap constraints for Bryan and Nicholas
    add_no_overlap_constraints(bryan_meetings, day, start_time, end_time)
    add_no_overlap_constraints(nicholas_meetings, day, start_time, end_time)

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        d = model[day].as_long()
        start = model[start_time].as_long()
        end = model[end_time].as_long()

        # Convert day number to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[d]

        # Convert start and end times to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        start_str = minutes_to_time(start)
        end_str = minutes_to_time(end)

        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling_problem()