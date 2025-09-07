from z3 import *

def main():
    opt = Optimize()

    # Define integer variables:
    # day: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday.
    # start: meeting start time in minutes from midnight.
    day = Int('day')
    start = Int('start')
    meeting_duration = 30
    end = start + meeting_duration

    # Working hours: between 9:00 (540 min) and 17:00 (1020 min)
    opt.add(day >= 0, day <= 4)
    opt.add(start >= 540, end <= 1020)

    # Frances would like to avoid Tuesday. (Tuesday is day 1)
    opt.add(day != 1)

    # Busy intervals given in (day, busy_start, busy_end) format in minutes.
    busy_intervals = [
        # Monday (day=0)
        (0, 630, 660),   # Terry: 10:30-11:00
        (0, 750, 840),   # Terry: 12:30-14:00
        (0, 900, 1020),  # Terry: 15:00-17:00
        (0, 570, 660),   # Frances: 9:30-11:00
        (0, 690, 780),   # Frances: 11:30-13:00
        (0, 840, 870),   # Frances: 14:00-14:30
        (0, 900, 960),   # Frances: 15:00-16:00

        # Tuesday (day=1)
        (1, 570, 600),   # Terry: 9:30-10:00
        (1, 630, 660),   # Terry: 10:30-11:00
        (1, 840, 870),   # Terry: 14:00-14:30
        (1, 960, 990),   # Terry: 16:00-16:30
        (1, 540, 570),   # Frances: 9:00-9:30
        (1, 600, 630),   # Frances: 10:00-10:30
        (1, 660, 720),   # Frances: 11:00-12:00
        (1, 780, 870),   # Frances: 13:00-14:30
        (1, 930, 990),   # Frances: 15:30-16:30

        # Wednesday (day=2)
        (2, 570, 630),   # Terry: 9:30-10:30
        (2, 660, 720),   # Terry: 11:00-12:00
        (2, 780, 810),   # Terry: 13:00-13:30
        (2, 900, 960),   # Terry: 15:00-16:00
        (2, 990, 1020),  # Terry: 16:30-17:00
        (2, 570, 600),   # Frances: 9:30-10:00
        (2, 630, 660),   # Frances: 10:30-11:00
        (2, 690, 960),   # Frances: 11:30-16:00
        (2, 990, 1020),  # Frances: 16:30-17:00

        # Thursday (day=3)
        (3, 570, 600),   # Terry: 9:30-10:00
        (3, 720, 750),   # Terry: 12:00-12:30
        (3, 780, 870),   # Terry: 13:00-14:30
        (3, 960, 990),   # Terry: 16:00-16:30
        (3, 660, 750),   # Frances: 11:00-12:30
        (3, 870, 1020),  # Frances: 14:30-17:00

        # Friday (day=4)
        (4, 540, 690),   # Terry: 9:00-11:30
        (4, 720, 750),   # Terry: 12:00-12:30
        (4, 810, 960),   # Terry: 13:30-16:00
        (4, 990, 1020),  # Terry: 16:30-17:00
        (4, 570, 630),   # Frances: 9:30-10:30
        (4, 660, 750),   # Frances: 11:00-12:30
        (4, 780, 960),   # Frances: 13:00-16:00
        (4, 990, 1020)   # Frances: 16:30-17:00
    ]

    # For each busy interval, if the meeting is on the same day, it must not overlap.
    for b_day, b_start, b_end in busy_intervals:
        opt.add(Or(day != b_day, end <= b_start, start >= b_end))

    # Optimize for the earliest meeting time.
    # We combine the day and start (in minutes) into a single objective to minimize.
    objective = day * 10000 + start
    opt.minimize(objective)

    if opt.check() == sat:
        model = opt.model()
        chosen_day = model[day].as_long()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + meeting_duration

        # Convert minutes to HH:MM format
        start_hour = meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = meeting_end // 60
        end_minute = meeting_end % 60

        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        # Output in the format: Day HH:MM:HH:MM
        print(f"{days[chosen_day]} {start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02}")
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()