from z3 import Solver, Int, Or, sat

def main():
    # Create a solver instance
    s = Solver()
    
    # Meeting duration (in minutes)
    duration = 30

    # Define the meeting start time as an integer representing minutes since midnight.
    meeting = Int('meeting')
    
    # Working hours on Monday: 09:00 (540 minutes) to 17:00 (1020 minutes)
    # Meeting must end by 17:00, so: meeting + duration <= 1020, and meeting >= 540.
    s.add(meeting >= 540, meeting + duration <= 1020)
    
    # To avoid overlap with a blocked interval [block_start, block_end),
    # the meeting [meeting, meeting+duration) must either end before block_start or start after block_end.
    def no_overlap(block_start, block_end):
        return Or(meeting + duration <= block_start, meeting >= block_end)
    
    # Blocked intervals for each participant (times in minutes since midnight)
    blocked_intervals = [
        # Diane's blocked times
        (570, 600),   # 09:30 - 10:00
        (870, 900),   # 14:30 - 15:00
        # Jack's blocked times
        (810, 840),   # 13:30 - 14:00
        (870, 900),   # 14:30 - 15:00
        # Eugene's blocked times
        (540, 600),   # 09:00 - 10:00
        (630, 690),   # 10:30 - 11:30
        (720, 870),   # 12:00 - 14:30
        (900, 990),   # 15:00 - 16:30
        # Patricia's blocked times
        (570, 630),   # 09:30 - 10:30
        (660, 720),   # 11:00 - 12:00
        (750, 840),   # 12:30 - 14:00
        (900, 990)    # 15:00 - 16:30
    ]
    
    # Add constraints for each blocked interval
    for start_block, end_block in blocked_intervals:
        s.add(no_overlap(start_block, end_block))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        meeting_start = m[meeting].as_long()
        meeting_end = meeting_start + duration
        
        # Convert minutes to HH:MM format
        start_hour = meeting_start // 60
        start_min = meeting_start % 60
        end_hour = meeting_end // 60
        end_min = meeting_end % 60
        
        # Output in the format HH:MM:HH:MM along with the day of the week
        print("{:02d}:{:02d}:{:02d}:{:02d} Monday".format(start_hour, start_min, end_hour, end_min))
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()