from z3 import *

def main():
    # We represent time in minutes from midnight.
    # 9:00 = 540 minutes, 17:00 = 1020 minutes, 12:30 = 750 minutes.
    duration = 30  # Meeting duration in minutes
    meeting_start = Int('meeting_start')
    meeting_end = meeting_start + duration

    solver = Solver()

    # Working hours constraint (meeting must be between 9:00 and 17:00)
    solver.add(meeting_start >= 540)          # meeting starts no earlier than 9:00
    solver.add(meeting_end <= 1020)             # meeting ends no later than 17:00

    # Jack's personal constraint: avoid meetings after 12:30
    # This means the meeting must end by 12:30.
    solver.add(meeting_end <= 750)

    # Busy intervals for Jack on Monday (in minutes after midnight)
    # 9:30-10:30, 11:00-11:30, 12:30-13:00, 14:00-14:30, 16:00-16:30
    jack_busy = [
        (570, 630),   # 9:30 to 10:30
        (660, 690),   # 11:00 to 11:30
        (750, 780),   # 12:30 to 13:00 (meeting ending at 750 is acceptable)
        (840, 870),   # 14:00 to 14:30
        (960, 990)    # 16:00 to 16:30
    ]

    # Busy intervals for Charlotte on Monday (in minutes after midnight)
    # 9:30-10:00, 10:30-12:00, 12:30-13:30, 14:00-16:00
    charlotte_busy = [
        (570, 600),   # 9:30 to 10:00
        (630, 720),   # 10:30 to 12:00
        (750, 810),   # 12:30 to 13:30
        (840, 960)    # 14:00 to 16:00
    ]

    # Add constraints: The meeting must not overlap any busy interval.
    # For each busy interval (s, e), the meeting must either finish by s or start at/after e.
    for (busy_start, busy_end) in jack_busy:
        solver.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))
        
    for (busy_start, busy_end) in charlotte_busy:
        solver.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

    if solver.check() == sat:
        model = solver.model()
        start_val = model[meeting_start].as_long()
        end_val = start_val + duration

        # Convert minutes into HH:MM format
        start_hour = start_val // 60
        start_minute = start_val % 60
        end_hour = end_val // 60
        end_minute = end_val % 60

        # Format the meeting time as "HH:MM:HH:MM"
        meeting_time = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        day = "Monday"
        print(f"{day} {meeting_time}")
    else:
        print("No valid meeting time could be found.")

if __name__ == "__main__":
    main()