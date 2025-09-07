from z3 import *

def schedule_meeting():
    # Meeting duration in minutes.
    duration = 30
    
    # Working hours on Monday:
    # Start: 9:00 (540 minutes) and End: 17:00 (1020 minutes)
    # However, Bobby prefers meetings to be scheduled before 15:00 (i.e., meeting must end by 15:00 or 900 minutes)
    work_start = 9 * 60      # 540
    preferred_end = 15 * 60  # 900

    # Define an integer variable for the meeting start time (in minutes since midnight)
    meeting_start = Int("meeting_start")
    
    s = Solver()
    # Meeting must start no earlier than work_start and finish by preferred_end.
    s.add(meeting_start >= work_start)
    s.add(meeting_start + duration <= preferred_end)
    
    # Busy intervals for each participant (in minutes since midnight)
    # Each busy interval is given as (start, end)
    # For non-overlap with a meeting interval [meeting_start, meeting_start+duration),
    # we require that either the meeting ends by the busy interval’s start OR
    # the meeting starts at or after the busy interval’s end.
    
    # Lisa's busy times: 9:00-10:00, 10:30-11:30, 12:30-13:00, 16:00-16:30
    lisa_busy = [
        (9 * 60, 10 * 60), 
        (10 * 60 + 30, 11 * 60 + 30), 
        (12 * 60 + 30, 13 * 60), 
        (16 * 60, 16 * 60 + 30)
    ]
    
    # Bobby's busy times: 9:00-9:30, 10:00-10:30, 11:30-12:00, 15:00-15:30
    bobby_busy = [
        (9 * 60, 9 * 60 + 30), 
        (10 * 60, 10 * 60 + 30), 
        (11 * 60 + 30, 12 * 60), 
        (15 * 60, 15 * 60 + 30)
    ]
    
    # Randy's busy times: 9:30-10:00, 10:30-11:00, 11:30-12:30, 13:00-13:30, 14:30-15:30, 16:00-16:30
    randy_busy = [
        (9 * 60 + 30, 10 * 60), 
        (10 * 60 + 30, 11 * 60), 
        (11 * 60 + 30, 12 * 60 + 30), 
        (13 * 60, 13 * 60 + 30), 
        (14 * 60 + 30, 15 * 60 + 30),
        (16 * 60, 16 * 60 + 30)
    ]
    
    # Helper function that returns a constraint stating that the meeting [m, m+duration)
    # does not overlap a busy interval [busy_start, busy_end)
    def no_overlap(busy_start, busy_end):
        return Or(meeting_start + duration <= busy_start, meeting_start >= busy_end)
    
    # Add non-overlap constraints for all busy intervals for each participant.
    for (start, end) in lisa_busy:
        s.add(no_overlap(start, end))
    for (start, end) in bobby_busy:
        s.add(no_overlap(start, end))
    for (start, end) in randy_busy:
        s.add(no_overlap(start, end))
    
    if s.check() == sat:
        m = s.model()
        start_time = m[meeting_start].as_long()
        end_time = start_time + duration
        
        # Convert minutes to HH:MM format.
        start_hour = start_time // 60
        start_minute = start_time % 60
        end_hour = end_time // 60
        end_minute = end_time % 60
        
        # Format the meeting time as HH:MM:HH:MM
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print("Monday", time_str)
    else:
        print("No solution found.")

if __name__ == "__main__":
    schedule_meeting()