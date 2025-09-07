from z3 import *

def main():
    meeting_duration = 60  # meeting lasts 60 minutes
    start = Int("start")   # meeting start time in minutes from midnight
    day = Int("day")       # day: Monday=0, Tuesday=1, Wednesday=2, Thursday=3

    s = Solver()

    # Working hours: between 9:00 (540 minutes) and 17:00 (1020 minutes)
    s.add(start >= 540)
    s.add(start + meeting_duration <= 1020)

    # Carl prefers to avoid Thursday, so restrict days to Monday, Tuesday, or Wednesday.
    s.add(Or(day == 0, day == 1, day == 2))

    # Define busy intervals as tuples: (day, busy_start, busy_end) in minutes from midnight.
    # Days: Monday=0, Tuesday=1, Wednesday=2, Thursday=3.
    busy_intervals = [
        # Monday: day == 0
        (0, 660, 690),   # Carl is busy Monday 11:00-11:30 (11*60=660, 11:30=690)
        (0, 540, 630),   # Margaret is busy Monday 9:00-10:30 (9:00=540, 10:30=630)
        (0, 660, 1020),  # Margaret is busy Monday 11:00-17:00 (11:00=660, 17:00=1020)

        # Tuesday: day == 1
        (1, 870, 900),   # Carl is busy Tuesday 14:30-15:00 (14:30=870, 15:00=900)
        (1, 570, 720),   # Margaret is busy Tuesday 9:30-12:00 (9:30=570, 12:00=720)
        (1, 810, 840),   # Margaret is busy Tuesday 13:30-14:00 (13:30=810, 14:00=840)
        (1, 930, 1020),  # Margaret is busy Tuesday 15:30-17:00 (15:30=930, 17:00=1020)

        # Wednesday: day == 2
        (2, 600, 690),   # Carl is busy Wednesday 10:00-11:30 (10:00=600, 11:30=690)
        (2, 780, 810),   # Carl is busy Wednesday 13:00-13:30 (13:00=780, 13:30=810)
        (2, 570, 720),   # Margaret is busy Wednesday 9:30-12:00 (9:30=570, 12:00=720)
        (2, 750, 780),   # Margaret is busy Wednesday 12:30-13:00 (12:30=750, 13:00=780)
        (2, 810, 870),   # Margaret is busy Wednesday 13:30-14:30 (13:30=810, 14:30=870)
        (2, 900, 1020),  # Margaret is busy Wednesday 15:00-17:00 (15:00=900, 17:00=1020)

        # Thursday intervals are defined but won't be used because we avoid Thursday:
        (3, 810, 840),   # Carl busy Thursday 13:30-14:00
        (3, 960, 990),   # Carl busy Thursday 16:00-16:30
        (3, 600, 720),   # Margaret busy Thursday 10:00-12:00
        (3, 750, 840),   # Margaret busy Thursday 12:30-14:00
        (3, 870, 1020)   # Margaret busy Thursday 14:30-17:00
    ]

    # For each busy interval, if the meeting is on that day, ensure no overlap.
    for (busy_day, busy_start, busy_end) in busy_intervals:
        s.add(Implies(day == busy_day, Or(start + meeting_duration <= busy_start, start >= busy_end)))

    if s.check() == sat:
        m = s.model()
        meeting_day = m[day].as_long()
        meeting_start = m[start].as_long()
        meeting_end = meeting_start + meeting_duration

        # Convert minutes to HH:MM format
        s_hour = meeting_start // 60
        s_min = meeting_start % 60
        e_hour = meeting_end // 60
        e_min = meeting_end % 60

        day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        chosen_day = day_names[meeting_day]

        # Output in the format: Day HH:MM:HH:MM
        print(f"{chosen_day} {s_hour:02d}:{s_min:02d}:{e_hour:02d}:{e_min:02d}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()