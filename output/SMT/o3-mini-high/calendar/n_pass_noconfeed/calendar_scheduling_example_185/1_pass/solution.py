from z3 import *

def main():
    s = Solver()
    
    # Define meeting start time as an integer number of minutes after 9:00.
    start = Int('start')
    duration = 30  # meeting duration in minutes

    # Working hours: meeting must finish by 17:00 => 480 minutes after 9:00.
    # Megan prefers to avoid meetings before 10:00, so meeting start must be at or after 10:00 (i.e. at least 60 minutes after 9:00).
    s.add(start >= 60, start + duration <= 480)

    # Busy intervals (in minutes after 9:00)
    # Kimberly: 10:00-10:30, 11:00-12:00, 16:00-16:30 -> (60,90), (120,180), (420,450)
    busy_intervals = [
        (60, 90),
        (120, 180),
        (420, 450),
    ]
    # Marie: 10:00-11:00, 11:30-15:00, 16:00-16:30 -> (60,120), (150,360), (420,450)
    busy_intervals += [
        (60, 120),
        (150, 360),
        (420, 450),
    ]
    # Diana: 9:30-10:00, 10:30-14:30, 15:30-17:00 -> (30,60), (90,330), (390,480)
    busy_intervals += [
        (30, 60),
        (90, 330),
        (390, 480),
    ]
    # Megan has no busy intervals.

    # For each busy interval, ensure the meeting does not overlap with it.
    # Two intervals [start, start+duration) and [b_start, b_end) do not overlap if:
    # meeting_end <= b_start OR meeting_start >= b_end
    for (b_start, b_end) in busy_intervals:
        s.add(Or(start + duration <= b_start, start >= b_end))

    if s.check() == sat:
        m = s.model()
        meeting_start = m[start].as_long()
        meeting_end = meeting_start + duration

        # Convert minutes (offset from 9:00) into actual clock times.
        start_total = 9 * 60 + meeting_start
        end_total = 9 * 60 + meeting_end
        
        start_hour = start_total // 60
        start_min = start_total % 60
        end_hour = end_total // 60
        end_min = end_total % 60

        # Format the meeting time as HH:MM:HH:MM.
        time_range = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        day = "Monday"

        print(f"{day} {time_range}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()