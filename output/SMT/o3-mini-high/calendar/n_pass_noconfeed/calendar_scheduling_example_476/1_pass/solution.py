from z3 import *

def minutes_to_time(offset):
    # Convert offset (in minutes from 9:00) to HH:MM format
    total_minutes = 9 * 60 + offset
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    duration = 30
    meeting_start = Int("meeting_start")
    solver = Solver()
    
    # Meeting must start and end during work hours (9:00 to 17:00).
    # The meeting must start no later than 16:30 -> offset 450.
    solver.add(meeting_start >= 0, meeting_start <= 450)
    
    # Roger's preference: do not meet before 12:30.
    # 12:30 is 210 minutes after 9:00.
    solver.add(meeting_start >= 210)
    
    # Busy intervals for each participant, measured as minutes from 9:00.
    # Each tuple represents (busy_start, busy_end).
    busy_intervals = [
        # Kathleen: 14:30–15:30 -> [330, 390]
        (330, 390),
        # Carolyn: 12:00–12:30 and 13:00–13:30 -> [180, 210] and [240, 270]
        (180, 210),
        (240, 270),
        # Cheryl: 9:00–9:30, 10:00–11:30, 12:30–13:30, 14:00–17:00 -> [0, 30], [60, 150], [210, 270], [300, 480]
        (0, 30),
        (60, 150),
        (210, 270),
        (300, 480),
        # Virginia: 9:30–11:30, 12:00–12:30, 13:00–13:30, 14:30–15:30, 16:00–17:00 -> [30, 150], [180, 210], [240, 270], [330, 390], [420, 480]
        (30, 150),
        (180, 210),
        (240, 270),
        (330, 390),
        (420, 480),
        # Angela: 9:30–10:00, 10:30–11:30, 12:00–12:30, 13:00–13:30, 14:00–16:30 -> [30, 60], [90, 150], [180, 210], [240, 270], [300, 450]
        (30, 60),
        (90, 150),
        (180, 210),
        (240, 270),
        (300, 450)
    ]
    
    # For each busy interval, add constraint that the meeting does not overlap.
    # That is, for each interval [b_start, b_end]:
    # Either the meeting finishes on or before b_start, or starts on or after b_end.
    for b_start, b_end in busy_intervals:
        solver.add(Or(meeting_start + duration <= b_start, meeting_start >= b_end))
    
    if solver.check() == sat:
        model = solver.model()
        start_val = model[meeting_start].as_long()
        start_str = minutes_to_time(start_val)
        end_str = minutes_to_time(start_val + duration)
        # Output format includes the day and time range in HH:MM:HH:MM format.
        print(f"Monday: {start_str}:{end_str}")
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()