from z3 import *

def main():
    # Create a Z3 solver instance
    solver = Solver()

    # Define the meeting start time T as minutes after 9:00.
    # Valid T must be such that the whole 30-minute meeting fits between 9:00 and 17:00.
    # Since 17:00 is 8 hours after 9:00 (480 minutes), we require: T in [0, 450]
    T = Int("T")
    meeting_duration = 30
    solver.add(T >= 0, T <= 480 - meeting_duration)

    # Define the busy intervals for each participant in minutes offset from 9:00.
    # Each tuple (a, b) means the person is busy from 9:00+a minutes to 9:00+b minutes.
    busy_intervals = [
        # Gregory: 9:00-9:30, 11:30-12:00
        (0, 30), (150, 180),
        # Jonathan: 9:00-9:30, 12:00-12:30, 13:00-13:30, 15:00-16:00, 16:30-17:00
        (0, 30), (180, 210), (240, 270), (360, 420), (450, 480),
        # Barbara: 10:00-10:30, 13:30-14:00
        (60, 90), (270, 300),
        # Jesse: 10:00-11:00, 12:30-14:30
        (60, 120), (210, 330),
        # Alan: 9:30-11:00, 11:30-12:30, 13:00-15:30, 16:00-17:00
        (30, 120), (150, 210), (240, 390), (420, 480),
        # Nicole: 9:00-10:30, 11:30-12:00, 12:30-13:30, 14:00-17:00
        (0, 90), (150, 180), (210, 270), (300, 480),
        # Catherine: 9:00-10:30, 12:00-13:30, 15:00-15:30, 16:00-16:30
        (0, 90), (180, 270), (360, 390), (420, 450)
    ]

    # For every busy interval [a, b), enforce that the meeting [T, T+30)
    # does NOT overlap with it. Two intervals do not overlap if:
    # meeting end <= busy interval start OR meeting start >= busy interval end.
    for (a, b) in busy_intervals:
        solver.add(Or(T + meeting_duration <= a, T >= b))

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start_offset = model[T].as_long()  # minutes after 9:00
        meeting_end_offset = meeting_start_offset + meeting_duration

        # Convert offsets to actual times
        base_hour = 9
        start_hour = base_hour + meeting_start_offset // 60
        start_minute = meeting_start_offset % 60
        end_hour = base_hour + meeting_end_offset // 60
        end_minute = meeting_end_offset % 60

        # Format the meeting time as HH:MM:HH:MM and include the day ("Monday")
        meeting_time = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        day = "Monday"
        print(f"{day} {meeting_time}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()