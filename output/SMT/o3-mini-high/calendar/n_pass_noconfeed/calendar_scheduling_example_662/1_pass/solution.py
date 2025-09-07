from z3 import Solver, Int, Or, Implies, sat

def main():
    s = Solver()
    # Define variables:
    # d: day indicator (0 for Monday, 1 for Tuesday)
    # start: meeting start time in minutes offset from 9:00 AM
    d = Int("d")
    start = Int("start")

    # Day must be either Monday (0) or Tuesday (1)
    s.add(Or(d == 0, d == 1))
    # The meeting lasts 60 minutes and must finish by 17:00 (which is 480 minutes after 9:00)
    # So start must be in [0, 420]
    s.add(start >= 0, start <= 420)
    meeting_duration = 60

    # Busy intervals are given in minutes relative to 9:00.
    # Monday busy intervals for Gary and David:
    monday_busy = [
        (0, 30),    # David: 09:00 - 09:30
        (30, 60),   # Gary: 09:30 - 10:00
        (60, 240),  # David: 10:00 - 13:00 (covers Gary's 11:00 - 13:00)
        (300, 330), # Gary: 14:00 - 14:30
        (330, 450), # David: 14:30 - 16:30
        (450, 480)  # Gary: 16:30 - 17:00
    ]

    # Tuesday busy intervals for Gary and David:
    tuesday_busy = [
        (0, 30),    # Both: 09:00 - 09:30
        (60, 90),   # David: 10:00 - 10:30
        (90, 120),  # Gary: 10:30 - 11:00
        (120, 210), # David: 11:00 - 12:30
        (240, 330), # David: 13:00 - 14:30
        (330, 420), # Gary: 14:30 - 16:00
        (360, 420), # David: 15:00 - 16:00 (redundant with above but harmless)
        (450, 480)  # David: 16:30 - 17:00
    ]

    # For each busy interval on Monday, if the meeting is scheduled on Monday then it must not overlap.
    for b_start, b_end in monday_busy:
        s.add(Implies(d == 0, Or(start + meeting_duration <= b_start, start >= b_end)))
        
    # For each busy interval on Tuesday, if the meeting is scheduled on Tuesday then it must not overlap.
    for b_start, b_end in tuesday_busy:
        s.add(Implies(d == 1, Or(start + meeting_duration <= b_start, start >= b_end)))

    if s.check() == sat:
        m = s.model()
        day_val = m[d].as_long()
        start_val = m[start].as_long()
        end_val = start_val + meeting_duration

        # Convert meeting start and end times to HH:MM (offset from 9:00 AM)
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60

        day_str = "Monday" if day_val == 0 else "Tuesday"
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Day: {day_str}, Time: {{{time_str}}}")
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()