from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the start time in minutes since midnight (9:00 is 540, 17:00 is 1020)
    start_time = Int('start_time')
    meeting_duration = 30  # minutes
    end_time = start_time + meeting_duration

    # Working hours: 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540)
    s.add(end_time <= 1020)

    # Janice's preference: meeting should end by 13:00 (780)
    s.add(end_time <= 780)

    # Participants' busy times in minutes since midnight
    # Each entry is (start, end)
    christine_busy = [
        (570, 630),   # 9:30-10:30
        (720, 750),   # 12:00-12:30
        (780, 810),   # 13:00-13:30
        (870, 900),   # 14:30-15:00
        (960, 990)    # 16:00-16:30
    ]
    bobby_busy = [
        (720, 750),   # 12:00-12:30
        (870, 900)    # 14:30-15:00
    ]
    elizabeth_busy = [
        (540, 570),    # 9:00-9:30
        (690, 780),    # 11:30-13:00
        (810, 840),    # 13:30-14:00
        (900, 930),    # 15:00-15:30
        (960, 1020)    # 16:00-17:00
    ]
    tyler_busy = [
        (540, 660),    # 9:00-11:00
        (720, 750),    # 12:00-12:30
        (780, 810),    # 13:00-13:30
        (930, 960),    # 15:30-16:00
        (990, 1020)    # 16:30-17:00
    ]
    edward_busy = [
        (540, 570),    # 9:00-9:30
        (600, 660),    # 10:00-11:00
        (690, 840),    # 11:30-14:00
        (870, 930),    # 14:30-15:30
        (960, 1020)    # 16:00-17:00
    ]

    # Function to add no-overlap constraints for a participant's busy times
    def add_no_overlap_constraints(busy_times):
        for busy_start, busy_end in busy_times:
            s.add(Or(end_time <= busy_start, start_time >= busy_end))

    # Add constraints for each participant
    add_no_overlap_constraints(christine_busy)
    add_no_overlap_constraints(bobby_busy)
    add_no_overlap_constraints(elizabeth_busy)
    add_no_overlap_constraints(tyler_busy)
    add_no_overlap_constraints(edward_busy)

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start_time].as_long()
        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_minutes + meeting_duration
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling_problem()