from z3 import Int, Optimize, Or, Implies

# A helper function to convert minutes since midnight to "HH:MM" format.
def minutes_to_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    opt = Optimize()

    # Create variables:
    # meeting_day: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    meeting_day = Int("meeting_day")
    meeting_start = Int("meeting_start")  # in minutes since midnight

    meeting_duration = 60  # in minutes
    meeting_end = meeting_start + meeting_duration

    # Work hours: meeting must be between 09:00 (540 min) and 17:00 (1020 min).
    # In order for a 60-minute meeting to finish by 17:00, meeting_start must be <= 1020 - 60 = 960.
    opt.add(meeting_day >= 0, meeting_day <= 3)
    opt.add(meeting_start >= 540, meeting_start <= 960)

    # Define the busy intervals for Megan and Daniel in minutes.
    # Each interval is a tuple (start, end) given in minutes from midnight.
    # Monday = 0, Tuesday = 1, Wednesday = 2, Thursday = 3.
    busy = {}

    # Monday:
    # Megan busy: 13:00-13:30 (780-810), 14:00-15:30 (840-930)
    # Daniel busy: 10:00-11:30 (600-690), 12:30-15:00 (750-900)
    busy[0] = [(780, 810), (840, 930), (600, 690), (750, 900)]

    # Tuesday:
    # Megan busy: 9:00-9:30 (540-570), 12:00-12:30 (720-750), 16:00-17:00 (960-1020)
    # Daniel busy: 9:00-10:00 (540-600), 10:30-17:00 (630-1020)
    busy[1] = [(540, 570), (720, 750), (960, 1020), (540, 600), (630, 1020)]

    # Wednesday:
    # Megan busy: 9:30-10:00 (570-600), 10:30-11:30 (630-690), 12:30-14:00 (750-840), 16:00-16:30 (960-990)
    # Daniel busy: 9:00-10:00 (540-600), 10:30-11:30 (630-690), 12:00-17:00 (720-1020)
    busy[2] = [(570, 600), (630, 690), (750, 840), (960, 990), (540, 600), (630, 690), (720, 1020)]

    # Thursday:
    # Megan busy: 13:30-14:30 (810-870), 15:00-15:30 (900-930)
    # Daniel busy: 9:00-12:00 (540-720), 12:30-14:30 (750-870), 15:00-15:30 (900-930), 16:00-17:00 (960-1020)
    busy[3] = [(810, 870), (900, 930), (540, 720), (750, 870), (900, 930), (960, 1020)]

    # For each day, if the meeting is on that day then it must not overlap any busy interval.
    # Two intervals [meeting_start, meeting_start+60) and [busy_start, busy_end) do not overlap
    # if either meeting_end <= busy_start or meeting_start >= busy_end.
    for d in range(4):
        for (busy_start, busy_end) in busy[d]:
            opt.add(Implies(meeting_day == d,
                            Or(meeting_start + meeting_duration <= busy_start,
                               meeting_start >= busy_end)))

    # We want the earliest available slot.
    # That means minimizing the day (Monday first) and then the start time.
    # We combine them into a single objective: meeting_day*10000 + meeting_start,
    # ensuring that day is prioritized over start time.
    objective = meeting_day * 10000 + meeting_start
    opt.minimize(objective)

    # Check for satisfiability.
    if opt.check() == 'sat':
        model = opt.model()
        d_val = model[meeting_day].as_long()
        start_val = model[meeting_start].as_long()
        end_val = start_val + meeting_duration

        # Map the integer day to the string day.
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        solution = "SOLUTION:\n"
        solution += f"Day: {days[d_val]}\n"
        solution += f"Start Time: {minutes_to_str(start_val)}\n"
        solution += f"End Time: {minutes_to_str(end_val)}"
        print(solution)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()