from z3 import *

def main():
    day = "Monday"
    work_start = 0  # 9:00 in minutes
    work_end = 480  # 17:00 in minutes (8 hours * 60 minutes)
    meeting_duration = 30  # minutes

    s = Solver()
    start = Int('start')

    # Constraint: Meeting must be within work hours
    s.add(start >= work_start)
    s.add(start + meeting_duration <= work_end)

    # Albert cannot meet after 11:00 (120 minutes from 9:00)
    s.add(start + meeting_duration <= 120)

    # Albert's busy intervals (in minutes from 9:00)
    albert_busy = [
        (0, 60),    # 9:00-10:00
        (90, 180),  # 10:30-12:00
        (360, 450)   # 15:00-16:30
    ]

    # Ensure no overlap with Albert's busy intervals
    for (busy_start, busy_end) in albert_busy:
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))

    if s.check() == sat:
        m = s.model()
        start_minutes = m.eval(start).as_long()

        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours}:{minutes:02d}"

        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{end_hours}:{end_minutes_remainder:02d}"

        print(f"Day: {day}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()