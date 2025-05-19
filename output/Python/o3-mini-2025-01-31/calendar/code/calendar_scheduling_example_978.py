from datetime import datetime, timedelta

# Convert time string HH:MM to minutes from midnight.
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Convert minutes from midnight to time string in HH:MM format.
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours in minutes (09:00 to 17:00)
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
MEETING_DURATION = 60  # in minutes

# Busy schedules for each participant per day.
# Times are represented as tuples of (start, end) in minutes.
# Monday, Tuesday, Wednesday, Thursday, Friday ordering.
brian_busy = {
    "Monday": [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    "Tuesday": [
        (time_to_minutes("09:00"), time_to_minutes("09:30"))
    ],
    "Wednesday": [
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    "Thursday": [
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    "Friday": [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

julia_busy = {
    "Monday": [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    "Tuesday": [
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    "Wednesday": [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("17:00"))
    ],
    "Thursday": [
        (time_to_minutes("09:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("17:00"))
    ],
    "Friday": [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ]
}

# List of weekdays. Given Brian prefers to avoid Monday, we try other days first.
weekdays_ordered = ["Tuesday", "Wednesday", "Thursday", "Friday", "Monday"]

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        prev = merged[-1]
        if current[0] <= prev[1]:
            merged[-1] = (prev[0], max(prev[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_slots(busy_intervals):
    """Based on busy intervals, compute free intervals within work hours."""
    free = []
    # Ensure the busy intervals are merged
    busy_intervals = merge_intervals(busy_intervals)
    start = WORK_START
    for interval in busy_intervals:
        if start < interval[0]:
            free.append((start, interval[0]))
        start = max(start, interval[1])
    if start < WORK_END:
        free.append((start, WORK_END))
    return free

def find_meeting_slot():
    for day in weekdays_ordered:
        # Get busy intervals for both participants on this day
        busy = []
        if day in brian_busy:
            busy.extend(brian_busy[day])
        if day in julia_busy:
            busy.extend(julia_busy[day])
        # Merge busy intervals and calculate free slots in work hours.
        free_slots = find_free_slots(busy)
        # Check for an available slot that is at least MEETING_DURATION long.
        for start, end in free_slots:
            if end - start >= MEETING_DURATION:
                # Return the earliest meeting slot (from start to start + duration)
                meeting_start = start
                meeting_end = start + MEETING_DURATION
                return day, minutes_to_time(meeting_start), minutes_to_time(meeting_end)
    return None, None, None

day, start_time, end_time = find_meeting_slot()
if day:
    # Output in the required format: HH:MM:HH:MM and day of the week.
    print(f"{start_time}:{end_time} on {day}")
else:
    print("No available slot found.")