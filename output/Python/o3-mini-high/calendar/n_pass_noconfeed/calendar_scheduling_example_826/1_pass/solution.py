def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def find_free_slot(busy_intervals, work_start, work_end, duration):
    # Start with the beginning of the work day
    current = work_start
    for start_busy, end_busy in sorted(busy_intervals):
        if start_busy - current >= duration:
            return current, current + duration
        current = max(current, end_busy)
    # Check after the last busy interval until work_end
    if work_end - current >= duration:
        return current, current + duration
    return None

# Meeting requirements
meeting_duration = 30  # in minutes
work_start = 9 * 60    # 9:00 in minutes (540)
work_end = 17 * 60     # 17:00 in minutes (1020)

# James' schedule for each day (times in minutes)
schedules = {
    "Monday": [
        (9*60 + 0, 9*60 + 30),
        (10*60 + 30, 11*60 + 0),
        (12*60 + 30, 13*60 + 0),
        (14*60 + 30, 15*60 + 30),
        (16*60 + 30, 17*60 + 0)
    ],
    "Tuesday": [
        (9*60 + 0, 11*60 + 0),
        (11*60 + 30, 12*60 + 0),
        (12*60 + 30, 15*60 + 30),
        (16*60 + 0, 17*60 + 0)
    ],
    "Wednesday": [
        (10*60 + 0, 11*60 + 0),
        (12*60 + 0, 13*60 + 0),
        (13*60 + 30, 16*60 + 0)
    ],
    "Thursday": [
        (9*60 + 30, 11*60 + 30),
        (12*60 + 0, 12*60 + 30),
        (13*60 + 0, 13*60 + 30),
        (14*60 + 0, 14*60 + 30),
        (16*60 + 30, 17*60 + 0)
    ]
}

# Cheryl's calendar is completely free.
# However, Cheryl prefers not to meet on Wednesday.
# Allowed days are Monday, Tuesday, Wednesday, or Thursday, so we check in this order:
preferred_days = ["Monday", "Tuesday", "Thursday", "Wednesday"]

scheduled = False

for day in preferred_days:
    busy = schedules.get(day, [])
    slot = find_free_slot(busy, work_start, work_end, meeting_duration)
    if slot:
        start, end = slot
        start_str = minutes_to_str(start)
        end_str = minutes_to_str(end)
        print(f"Meeting scheduled on {day}: {start_str}:{end_str}")
        scheduled = True
        break

if not scheduled:
    print("No available meeting slot found.")