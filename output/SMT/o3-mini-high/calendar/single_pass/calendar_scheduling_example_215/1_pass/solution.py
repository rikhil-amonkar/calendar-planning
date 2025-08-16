from z3 import Int, Optimize, Or, sat

def minutes_to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    meeting_duration = 30  # meeting length in minutes
    # meeting_start is the start time measured in minutes after midnight.
    meeting_start = Int("meeting_start")
    
    # Working day: Monday 09:00 to 17:00.
    work_start = 9 * 60   # 09:00 is 540 minutes after midnight
    work_end = 17 * 60    # 17:00 is 1020 minutes after midnight

    opt = Optimize()
    # The meeting must start and end within working hours.
    opt.add(meeting_start >= work_start, meeting_start + meeting_duration <= work_end)
    
    # Define busy intervals as tuples of (start_in_minutes, end_in_minutes)
    # All times are in minutes after midnight.
    busy_intervals = [
        # Cynthia's busy times
        (9 * 60 + 30, 10 * 60 + 30),   # 09:30 - 10:30 -> (570, 630)
        (11 * 60 + 30, 12 * 60),        # 11:30 - 12:00 -> (690, 720)
        (13 * 60, 13 * 60 + 30),        # 13:00 - 13:30 -> (780, 810)
        (15 * 60, 16 * 60),             # 15:00 - 16:00 -> (900, 960)
        
        # Lauren's busy times
        (9 * 60, 9 * 60 + 30),          # 09:00 - 09:30 -> (540, 570)
        (10 * 60 + 30, 11 * 60),         # 10:30 - 11:00 -> (630, 660)
        (11 * 60 + 30, 12 * 60),         # 11:30 - 12:00 -> (690, 720)
        (13 * 60, 13 * 60 + 30),         # 13:00 - 13:30 -> (780, 810)
        (14 * 60, 14 * 60 + 30),         # 14:00 - 14:30 -> (840, 870)
        (15 * 60, 15 * 60 + 30),         # 15:00 - 15:30 -> (900, 930)
        (16 * 60, 17 * 60),             # 16:00 - 17:00 -> (960, 1020)
        
        # Robert's busy times
        (10 * 60 + 30, 11 * 60),        # 10:30 - 11:00 -> (630, 660)
        (11 * 60 + 30, 12 * 60),        # 11:30 - 12:00 -> (690, 720)
        (12 * 60 + 30, 13 * 60 + 30),    # 12:30 - 13:30 -> (750, 810)
        (14 * 60, 16 * 60),             # 14:00 - 16:00 -> (840, 960)
    ]
    
    # For each busy interval, add a constraint so that the meeting does not overlap the busy time.
    # A meeting (from meeting_start to meeting_start+duration) does not overlap an interval (s, e)
    # if either it ends by the start (meeting_start + duration <= s) or it starts after the interval (meeting_start >= e).
    for (busy_start, busy_end) in busy_intervals:
        opt.add(Or(meeting_start + meeting_duration <= busy_start,
                   meeting_start >= busy_end))
    
    # Since Steven and Roy have no meetings, no extra constraints are needed for them.

    # We want the earliest possible meeting: minimize meeting_start.
    opt.minimize(meeting_start)
    
    # Check and get the model.
    if opt.check() == sat:
        model = opt.model()
        start_val = model[meeting_start].as_long()
        end_val = start_val + meeting_duration
        
        # Format the times as HH:MM in 24-hour format.
        start_time_str = minutes_to_hhmm(start_val)
        end_time_str = minutes_to_hhmm(end_val)
        
        # Print the solution in the required format.
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()