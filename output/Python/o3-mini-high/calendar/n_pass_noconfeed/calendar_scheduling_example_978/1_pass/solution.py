def time_to_minutes(t):
    """Converts a time string 'HH:MM' to minutes past midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Converts minutes past midnight to a time string 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    """Given a sorted list of busy intervals, returns free intervals within work hours."""
    free = []
    # If no busy intervals, the entire work day is free.
    if not busy:
        free.append((work_start, work_end))
        return free

    # Before the first busy interval.
    if busy[0][0] > work_start:
        free.append((work_start, busy[0][0]))

    # Between busy intervals.
    for i in range(len(busy) - 1):
        if busy[i][1] < busy[i+1][0]:
            free.append((busy[i][1], busy[i+1][0]))

    # After the last busy interval.
    if busy[-1][1] < work_end:
        free.append((busy[-1][1], work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Intersects two lists of intervals."""
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap.
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersections.append((start, end))
        # Move to next interval from the one that ends earlier.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Define work hours and meeting duration.
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Define the busy schedules for Brian and Julia.
schedule = {
    "Monday": {
        "Brian": [
            (time_to_minutes("09:30"), time_to_minutes("10:00")),
            (time_to_minutes("12:30"), time_to_minutes("14:30")),
            (time_to_minutes("15:30"), time_to_minutes("16:00"))
        ],
        "Julia": [
            (time_to_minutes("09:00"), time_to_minutes("10:00")),
            (time_to_minutes("11:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:30"), time_to_minutes("13:00")),
            (time_to_minutes("15:30"), time_to_minutes("16:00"))
        ]
    },
    "Tuesday": {
        "Brian": [
            (time_to_minutes("09:00"), time_to_minutes("09:30"))
        ],
        "Julia": [
            (time_to_minutes("13:00"), time_to_minutes("14:00")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    },
    "Wednesday": {
        "Brian": [
            (time_to_minutes("12:30"), time_to_minutes("14:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ],
        "Julia": [
            (time_to_minutes("09:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("17:00"))
        ]
    },
    "Thursday": {
        "Brian": [
            (time_to_minutes("11:00"), time_to_minutes("11:30")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ],
        "Julia": [
            (time_to_minutes("09:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:00"), time_to_minutes("17:00"))
        ]
    },
    "Friday": {
        "Brian": [
            (time_to_minutes("09:30"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("11:00")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("15:00"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ],
        "Julia": [
            (time_to_minutes("09:00"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("11:30")),
            (time_to_minutes("12:30"), time_to_minutes("14:00")),
            (time_to_minutes("14:30"), time_to_minutes("15:00")),
            (time_to_minutes("15:30"), time_to_minutes("16:00"))
        ]
    }
}

def find_meeting_for_day(day):
    """Returns a possible (start, end) meeting time for a given day or None if unavailable."""
    brian_busy = schedule[day]["Brian"]
    julia_busy = schedule[day]["Julia"]
    brian_free = get_free_intervals(sorted(brian_busy), work_start, work_end)
    julia_free = get_free_intervals(sorted(julia_busy), work_start, work_end)
    common_free = intersect_intervals(brian_free, julia_free)
    for (s, e) in common_free:
        if (e - s) >= meeting_duration:
            return s, s + meeting_duration
    return None

# Preferred days (avoid Monday if possible).
preferred_days = ["Tuesday", "Wednesday", "Thursday", "Friday"]
fallback_days = ["Monday"]

meeting_day = None
meeting_start_time = None
meeting_end_time = None

# Try preferred days first.
for day in preferred_days:
    result = find_meeting_for_day(day)
    if result:
        meeting_day = day
        meeting_start_time, meeting_end_time = result
        break

# If no meeting found on preferred days, check Monday.
if meeting_day is None:
    for day in fallback_days:
        result = find_meeting_for_day(day)
        if result:
            meeting_day = day
            meeting_start_time, meeting_end_time = result
            break

if meeting_day:
    start_str = minutes_to_time(meeting_start_time)
    end_str = minutes_to_time(meeting_end_time)
    # Output format: "Day HH:MM:HH:MM"
    print(f"{meeting_day} {start_str}:{end_str}")
else:
    print("No available meeting time found.")