from z3 import *

def main():
    # Define meeting start time (in minutes since midnight)
    meeting_start = Int('meeting_start')
    duration = 30  # meeting duration in minutes

    # Working hours: 9:00 is 540 minutes and 17:00 is 1020 minutes.
    # The meeting must finish by 17:00.
    s = Solver()
    s.add(meeting_start >= 540)
    s.add(meeting_start + duration <= 1020)
    
    # Busy intervals for each participant (times in minutes since midnight)
    # Andrea: 9:30-10:30, 13:30-14:30
    # Ruth: 12:30-13:00, 15:00-15:30
    # Steven: 10:00-10:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 15:00-16:00
    # Grace: free the whole day
    # Kyle: 9:00-9:30, 10:30-12:00, 12:30-13:00, 13:30-15:00, 15:30-16:00, 16:30-17:00
    # Elijah: 9:00-11:00, 11:30-13:00, 13:30-14:00, 15:30-16:00, 16:30-17:00
    # Lori: 9:00-9:30, 10:00-11:30, 12:00-13:30, 14:00-16:00, 16:30-17:00
    
    # Convert times to minutes:
    busy_intervals = [
        # Andrea
        (570, 630), (810, 870),
        # Ruth
        (750, 780), (900, 930),
        # Steven
        (600, 630), (660, 690), (720, 750), (810, 840), (900, 960),
        # Kyle
        (540, 570), (630, 720), (750, 780), (810, 900), (930, 960), (990, 1020),
        # Elijah
        (540, 660), (690, 780), (810, 840), (930, 960), (990, 1020),
        # Lori
        (540, 570), (600, 690), (720, 810), (840, 960), (990, 1020)
    ]
    
    # For each busy interval, add the constraint that the meeting must not overlap it.
    # That is: either the meeting ends on or before the busy interval begins,
    # or it starts on or after the busy interval ends.
    for (busy_start, busy_end) in busy_intervals:
        s.add(Or(meeting_start + duration <= busy_start, meeting_start >= busy_end))
    
    if s.check() == sat:
        model = s.model()
        start_min = model[meeting_start].as_long()
        end_min = start_min + duration
        
        # Format a time in HH:MM (24-hour format) from minutes since midnight.
        def format_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"
        
        # Output the solution in the required format.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time:", format_time(start_min))
        print("End Time:", format_time(end_min))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()