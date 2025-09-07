from z3 import Optimize, Int, Or, sat

def main():
    # Create an optimization solver (to minimize meeting start time)
    opt = Optimize()

    # The meeting duration is 30 minutes.
    duration = 30

    # meeting_start is the number of minutes after 9:00.
    meeting_start = Int("meeting_start")
    meeting_end = meeting_start + duration

    # Workday: 9:00 (0 minutes) to 17:00 (480 minutes)
    opt.add(meeting_start >= 0)
    opt.add(meeting_end <= 480)

    # Samuel's blocked intervals (in minutes from 9:00):
    # 9:00 - 10:30  => 0 to 90
    # 11:30 - 12:00 => 150 to 180
    # 13:00 - 13:30 => 240 to 270
    # 14:00 - 16:00 => 300 to 420
    # 16:30 - 17:00 => 450 to 480
    blocked_intervals = [
        (0, 90),
        (150, 180),
        (240, 270),
        (300, 420),
        (450, 480)
    ]

    # For each blocked interval, ensure the meeting does not overlap
    for (block_start, block_end) in blocked_intervals:
        # The meeting must either finish by block_start or start after block_end
        opt.add(Or(meeting_end <= block_start, meeting_start >= block_end))

    # We desire the earliest available meeting time so minimize meeting_start.
    opt.minimize(meeting_start)

    # Check if the constraints are satisfiable and extract the model.
    if opt.check() == sat:
        model = opt.model()
        start_val = model[meeting_start].as_long()  # meeting start in minutes after 9:00
        end_val = start_val + duration

        # Convert minutes-after-9:00 to actual time (HH:MM)
        # The meeting starts at 9:00 + start_val minutes
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60

        # Format the meeting time as HH:MM:HH:MM
        meeting_time = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        day = "Monday"

        print(meeting_time)
        print(day)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()