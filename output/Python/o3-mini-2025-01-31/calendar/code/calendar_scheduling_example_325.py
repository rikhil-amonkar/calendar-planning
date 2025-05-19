from datetime import timedelta, datetime

# Helper function: convert HH:MM string to minutes from midnight
def to_minutes(time_str):
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

# Helper function: convert minutes from midnight to HH:MM string
def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Given the work day and constraints:
# Work hours: 09:00 (540 minutes) to 17:00 (1020 minutes)
# But Jose does not want to meet after 15:30 so effectively his window is 09:00 to 15:30 (930 minutes).
# Meeting duration in minutes:
meeting_duration = 30

# For each participant we've been given busy intervals.
# We will first define each participant's busy intervals (in minutes) for Monday.
# Note: Times are in the format [start, end) in minutes.
schedules = {
    "Jose": [
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("12:30"), to_minutes("13:00"))
    ],
    "Keith": [
        (to_minutes("14:00"), to_minutes("14:30")),
        (to_minutes("15:00"), to_minutes("15:30"))
    ],
    "Logan": [
        (to_minutes("09:00"), to_minutes("10:00")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("15:00"), to_minutes("15:30"))
    ],
    "Megan": [
        (to_minutes("09:00"), to_minutes("10:30")),
        (to_minutes("11:00"), to_minutes("12:00")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:30"), to_minutes("16:30"))
    ],
    "Gary": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:00"), to_minutes("10:30")),
        (to_minutes("11:30"), to_minutes("13:00")),
        (to_minutes("13:30"), to_minutes("14:00")),
        (to_minutes("14:30"), to_minutes("16:30"))
    ],
    "Bobby": [
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("16:00"))
    ]
}

# Work window for each participant.
# For everyone except Jose, the work window is 09:00 (540) to 17:00 (1020),
# but for scheduling the meeting we must consider only slots that also respect Jose's constraint: meeting end before or at 15:30 (930).
work_window_start = to_minutes("09:00")
work_window_end = to_minutes("17:00")
jose_latest_end = to_minutes("15:30")
# For meeting scheduling, the effective overall time window becomes:
effective_start = work_window_start
effective_end = min(work_window_end, jose_latest_end)  # 15:30 = 930

# Function to compute free intervals given a list of busy intervals and a work window.
def compute_free_intervals(busy_intervals, window_start, window_end):
    # Sort busy intervals by start time
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    
    # Start with the time from window_start to the first busy interval
    current = window_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        # Move current pointer to the maximum of current or end of the busy interval
        current = max(current, end)
    # Add remaining time after last busy event
    if current < window_end:
        free_intervals.append((current, window_end))
    return free_intervals

# Compute free intervals for each participant within their effective window.
# Note: For Jose we restrict his window to effective_start to jose_latest_end.
free_times = {}
for person, busy in schedules.items():
    if person == "Jose":
        free_times[person] = compute_free_intervals(busy, effective_start, jose_latest_end)
    else:
        free_times[person] = compute_free_intervals(busy, effective_start, effective_end)

# For debugging, you can print each person's free intervals in HH:MM format.
# for person, intervals in free_times.items():
#     print(person, [(to_time_str(start), to_time_str(end)) for start, end in intervals])

# Function to intersect two lists of intervals.
def intersect_intervals(list1, list2):
    result = []
    i, j = 0, 0
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        # Calculate the overlap between intervals:
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:  # There is an overlap
            result.append((start, end))
        # Move to the next interval in the list that finishes first.
        if a_end <= b_end:
            i += 1
        else:
            j += 1
    return result

# Compute the overall intersection of free intervals for all participants.
participants = list(free_times.keys())
common_free = free_times[participants[0]]
for person in participants[1:]:
    common_free = intersect_intervals(common_free, free_times[person])

# Find a common free interval that is at least meeting_duration long.
proposed_interval = None
for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_interval = (start, start + meeting_duration)
        break

if proposed_interval is not None:
    start_time_str = to_time_str(proposed_interval[0])
    end_time_str = to_time_str(proposed_interval[1])
    # Make sure the output format is as required: HH:MM:HH:MM and include the day of the week.
    print(f"Monday {start_time_str}:{end_time_str}")
else:
    print("No available slot found.")