from z3 import *

def main():
    s = Solver()
    
    # meeting_start is in minutes since midnight.
    meeting_start = Int('meeting_start')
    duration = 60
    meeting_end = meeting_start + duration

    # Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
    s.add(meeting_start >= 540, meeting_start <= 1020 - duration)
    
    # Busy intervals for each participant on Monday (in minutes)
    busy_intervals = [
        # Joshua's busy times: 11:00-12:30, 13:30-14:30, 16:30-17:00
        (660, 750),
        (810, 870),
        (990, 1020),
        
        # Jerry's busy times: 9:00-9:30, 10:30-12:00, 12:30-13:00,
        # 13:30-14:00, 14:30-15:00, 15:30-16:00
        (540, 570),
        (630, 720),
        (750, 780),
        (810, 840),
        (870, 900),
        (930, 960),
        
        # Jesse's busy times: 9:00-9:30, 10:30-12:00, 12:30-13:00,
        # 14:30-15:00, 15:30-16:30
        (540, 570),
        (630, 720),
        (750, 780),
        (870, 900),
        (930, 990),
        
        # Kenneth's busy times: 10:30-12:30, 13:30-14:00, 14:30-15:00,
        # 15:30-16:00, 16:30-17:00
        (630, 750),
        (810, 840),
        (870, 900),
        (930, 960),
        (990, 1020)
    ]
    
    # For each busy interval [a, b), the meeting must not overlap. 
    # That is, we add: meeting_end <= a  or  meeting_start >= b.
    for (busy_start, busy_end) in busy_intervals:
        s.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))
    
    if s.check() == sat:
        m = s.model()[meeting_start].as_long()
        meet_start = m
        meet_end = m + duration
        
        def minutes_to_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        start_str = minutes_to_str(meet_start)
        end_str = minutes_to_str(meet_end)
        
        # Output the meeting time range and the day of the week "Monday"
        print(f"{start_str}:{end_str} Monday")
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()