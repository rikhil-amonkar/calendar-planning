from z3 import *

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Meeting duration and working hours (in minutes)
    meeting_duration = 30
    work_start = 9 * 60       # 9:00 -> 540
    work_end = 17 * 60        # 17:00 -> 1020

    # Create Z3 solver and meeting start time variable
    s = Solver()
    meeting_start = Int("meeting_start")
    
    # Meeting must start and finish within working hours
    s.add(meeting_start >= work_start)
    s.add(meeting_start + meeting_duration <= work_end)
    
    # Busy intervals (in minutes) for each participant on Monday
    busy_intervals = [
        # Megan busy: 9:00-9:30, 10:00-11:00, 12:00-12:30
        (9 * 60,      9 * 60 + 30),   # (540, 570)
        (10 * 60,     11 * 60),       # (600, 660)
        (12 * 60,     12 * 60 + 30),  # (720, 750)
        
        # Christine busy: 9:00-9:30, 11:30-12:00, 13:00-14:00, 15:30-16:30
        (9 * 60,      9 * 60 + 30),   # (540, 570)
        (11 * 60 + 30, 12 * 60),       # (690, 720)
        (13 * 60,     14 * 60),       # (780, 840)
        (15 * 60 + 30, 16 * 60 + 30),  # (930, 990)
        
        # Sara busy: 11:30-12:00, 14:30-15:00
        (11 * 60 + 30, 12 * 60),       # (690, 720)
        (14 * 60 + 30, 15 * 60),       # (870, 900)
        
        # Bruce busy: 9:30-10:00, 10:30-12:00, 12:30-14:00, 14:30-15:00, 15:30-16:30
        (9 * 60 + 30, 10 * 60),        # (570, 600)
        (10 * 60 + 30, 12 * 60),       # (630, 720)
        (12 * 60 + 30, 14 * 60),       # (750, 840)
        (14 * 60 + 30, 15 * 60),       # (870, 900)
        (15 * 60 + 30, 16 * 60 + 30),  # (930, 990)
        
        # Kathryn busy: 10:00-15:30, 16:00-16:30
        (10 * 60,     15 * 60 + 30),   # (600, 930)
        (16 * 60,     16 * 60 + 30),   # (960, 990)
        
        # Billy busy: 9:00-9:30, 11:00-11:30, 12:00-14:00, 14:30-15:30
        (9 * 60,      9 * 60 + 30),    # (540, 570)
        (11 * 60,     11 * 60 + 30),   # (660, 690)
        (12 * 60,     14 * 60),        # (720, 840)
        (14 * 60 + 30, 15 * 60 + 30)    # (870, 930)
    ]
    
    # Add non-overlap constraints for each busy interval.
    # The meeting (from meeting_start to meeting_start+duration) must either finish
    # before a busy interval starts or start after it ends.
    for (busy_start, busy_end) in busy_intervals:
        s.add(Or(meeting_start + meeting_duration <= busy_start,
                 meeting_start >= busy_end))
    
    if s.check() == sat:
        model = s.model()
        start = model[meeting_start].as_long()
        end = start + meeting_duration
        day = "Monday"
        # Output in the format HH:MM-HH:MM on Day
        print(f"{minutes_to_time_str(start)}-{minutes_to_time_str(end)} on {day}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()