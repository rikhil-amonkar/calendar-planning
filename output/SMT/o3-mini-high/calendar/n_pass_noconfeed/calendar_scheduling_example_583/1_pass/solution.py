from z3 import Optimize, Int, Or, sat

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def schedule_meeting():
    # Create an optimizer instance for minimizing the meeting start time
    opt = Optimize()

    meeting_duration = 30  # in minutes
    meeting_start = Int('meeting_start')  # meeting start time in minutes from midnight
    
    # Define working hours: 9:00 (540) to 17:00 (1020)
    work_start = 9 * 60         # 9:00 in minutes
    work_end = 17 * 60          # 17:00 in minutes
    # The meeting must finish by work_end, so meeting_start + duration <= 1020
    opt.add(meeting_start >= work_start, meeting_start + meeting_duration <= work_end)
    
    # Define busy intervals (in minutes from midnight) for each participant on Monday
    busy_intervals = [
        # Lisa's busy times:
        (9 * 60, 9 * 60 + 30),        # 9:00 - 9:30
        (10 * 60 + 30, 11 * 60),        # 10:30 - 11:00
        (14 * 60, 16 * 60),             # 14:00 - 16:00
        # Anthony's busy times:
        (9 * 60, 9 * 60 + 30),          # 9:00 - 9:30
        (11 * 60, 11 * 60 + 30),        # 11:00 - 11:30
        (12 * 60 + 30, 13 * 60 + 30),    # 12:30 - 13:30
        (14 * 60, 15 * 60),             # 14:00 - 15:00
        (15 * 60 + 30, 16 * 60),         # 15:30 - 16:00
        (16 * 60 + 30, 17 * 60)          # 16:30 - 17:00
    ]
    
    # For each busy interval, add a constraint that the meeting does not overlap it.
    # The meeting [meeting_start, meeting_start+duration) must be either completely before the busy interval 
    # or completely after it.
    for (busy_start, busy_end) in busy_intervals:
        opt.add(Or(meeting_start + meeting_duration <= busy_start, meeting_start >= busy_end))
    
    # Since we want the earliest available slot, we minimize the meeting_start.
    opt.minimize(meeting_start)
    
    if opt.check() == sat:
        model = opt.model()
        start_val = model[meeting_start].as_long()
        end_val = start_val + meeting_duration
        
        start_str = minutes_to_time_str(start_val)
        end_str = minutes_to_time_str(end_val)
        day = "Monday"
        # Output in the format HH:MM:HH:MM along with the day of the week
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No solution found.")

if __name__ == '__main__':
    schedule_meeting()