def time_to_minutes(t):
    """Converts time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Converts minutes since midnight to time string 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def subtract_busy(interval, busys):
    """
    Given an interval (start, end) and a sorted list of busy intervals,
    subtracts out busy periods to return a list of free intervals.
    """
    free = []
    start, end = interval
    current = start
    for bstart, bend in busys:
        if bend <= current:
            continue
        if bstart > current:
            free.append((current, min(bstart, end)))
        current = max(current, bend)
        if current >= end:
            break
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, return their intersection.
    Each interval is a tuple (start, end).
    """
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

# Meeting constraints
meeting_duration = 30  # minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Define each person's busy schedule as dictionary of day->list of (start, end) in minutes
schedules = {
    "Monday": {
        "Mary": [],  # Mary has no meetings on Monday.
        "Alexis": [
            (time_to_minutes("09:00"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("12:00")),
            (time_to_minutes("12:30"), time_to_minutes("16:30"))
        ]
    },
    "Tuesday": {
        "Mary": [
            (time_to_minutes("10:00"), time_to_minutes("10:30")),
            (time_to_minutes("15:30"), time_to_minutes("16:00"))
        ],
        "Alexis": [
            (time_to_minutes("09:00"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("17:00"))
        ]
    },
    "Wednesday": {
        "Mary": [
            (time_to_minutes("09:30"), time_to_minutes("10:00")),
            (time_to_minutes("15:00"), time_to_minutes("15:30"))
        ],
        "Alexis": [
            (time_to_minutes("09:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("17:00"))
        ]
    },
    "Thursday": {
        "Mary": [
            (time_to_minutes("09:00"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("11:30"))
        ],
        "Alexis": [
            (time_to_minutes("10:00"), time_to_minutes("12:00")),
            (time_to_minutes("14:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:30"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ]
    }
}

days_order = ["Monday", "Tuesday", "Wednesday", "Thursday"]

earliest_meeting = None
meeting_day = None

for day in days_order:
    # For each participant, determine free intervals by subtracting busy time from working hours.
    free_intervals = {}
    for person in schedules[day]:
        busy_times = sorted(schedules[day][person])
        free_intervals[person] = subtract_busy((work_start, work_end), busy_times)
    
    # Find common free intervals between all participants.
    # Start with the free intervals for the first participant.
    persons = list(free_intervals.keys())
    common_free = free_intervals[persons[0]]
    for person in persons[1:]:
        common_free = intersect_intervals(common_free, free_intervals[person])
    
    # Check if there is an interval with at least meeting_duration minutes.
    for start, end in common_free:
        if end - start >= meeting_duration:
            earliest_meeting = (start, start + meeting_duration)
            meeting_day = day
            break
    if earliest_meeting:
        break

if earliest_meeting and meeting_day:
    start_time = minutes_to_time(earliest_meeting[0])
    end_time = minutes_to_time(earliest_meeting[1])
    print(f"{meeting_day}, {start_time}:{end_time}")
else:
    print("No available meeting time could be found.")