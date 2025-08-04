from z3 import *

def solve_meeting_schedule():
    # Participants' busy slots in HH:MM format (converted to minutes since 9:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30        # meeting duration in minutes

    # Each participant's busy slots in minutes since 9:00
    # Format: list of (start, end) tuples
    gregory = [(0, 30), (150, 180)]  # 9:00-9:30, 11:30-12:00
    jonathan = [(0, 30), (180, 210), (240, 270), (360, 420), (450, 480)]  # 9:00-9:30, 12:00-12:30, 13:00-13:30, 15:00-16:00, 16:30-17:00
    barbara = [(60, 90), (270, 300)]  # 10:00-10:30, 13:30-14:00
    jesse = [(60, 120), (210, 330)]   # 10:00-11:00, 12:30-14:30
    alan = [(30, 120), (150, 210), (240, 390), (420, 480)]  # 9:30-11:00, 11:30-12:30, 13:00-15:30, 16:00-17:00
    nicole = [(0, 90), (150, 180), (210, 270), (300, 480)]  # 9:00-10:30, 11:30-12:00, 12:30-13:30, 14:00-17:00
    catherine = [(0, 90), (180, 270), (360, 390), (420, 450)]  # 9:00-10:30, 12:00-13:30, 15:00-15:30, 16:00-16:30

    participants = [gregory, jonathan, barbara, jesse, alan, nicole, catherine]

    # Create Z3 solver
    s = Solver()

    # Meeting start time in minutes since 9:00
    start = Int('start')
    end = start + duration

    # Constraints: start and end within work hours
    s.add(start >= work_start - work_start)  # 0, since work_start is 9:00 (0 minutes after 9:00)
    s.add(end <= work_end - work_start)      # 480 minutes (17:00 is 8 hours after 9:00)

    # For each participant, the meeting must not overlap with any of their busy slots
    for person in participants:
        for (busy_start, busy_end) in person:
            # The meeting is either entirely before or entirely after the busy slot
            s.add(Or(end <= busy_start, start >= busy_end))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_time_min = m[start].as_long()
        # Convert start time back to HH:MM
        total_min = work_start + start_time_min
        hours = total_min // 60
        minutes = total_min % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        end_time_min = total_min + duration
        end_hours = end_time_min // 60
        end_minutes = end_time_min % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        print(f"SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_meeting_schedule()