from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define the start time variable (in minutes from 9:00)
    start = Int('start')
    
    # Work hours: 9:00 to 17:00 (480 minutes). Meeting duration is 30 minutes.
    s.add(start >= 0)
    s.add(start <= 450)  # 480 - 30 = 450 minutes (16:30)
    
    # Jack's busy intervals (each as (start_minute, end_minute))
    jack_busy = [(30, 90), (120, 150), (210, 240), (300, 330), (420, 450)]
    for (b_start, b_end) in jack_busy:
        s.add(Or(start + 30 <= b_start, start >= b_end))
    
    # Charlotte's busy intervals
    charlotte_busy = [(30, 60), (90, 180), (210, 270), (300, 420)]
    for (b_start, b_end) in charlotte_busy:
        s.add(Or(start + 30 <= b_start, start >= b_end))
    
    # First, try to satisfy Jack's preference: meeting ends by 12:30 (210 minutes from 9:00)
    s.push()
    s.add(start + 30 <= 210)
    
    # Check for a solution with the preference
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
    else:
        # If no solution with preference, try without
        s.pop()
        if s.check() == sat:
            m = s.model()
            start_val = m[start].as_long()
        else:
            # According to the problem, a solution exists, so this should not happen
            start_val = 0
    
    # Convert start time from minutes to HH:MM format
    total_minutes_start = 9 * 60 + start_val
    hours_start = total_minutes_start // 60
    minutes_start = total_minutes_start % 60
    start_time = f"{hours_start}:{minutes_start:02d}"
    
    # Calculate end time
    end_val = start_val + 30
    total_minutes_end = 9 * 60 + end_val
    hours_end = total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    end_time = f"{hours_end}:{minutes_end:02d}"
    
    # Output the solution
    print(f"Monday {start_time} {end_time}")

if __name__ == "__main__":
    main()