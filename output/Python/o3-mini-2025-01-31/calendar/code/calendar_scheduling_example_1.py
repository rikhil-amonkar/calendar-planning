from datetime import datetime, timedelta

def time_to_minutes(time_str):
    # time_str is in HH:MM format
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    # convert minutes (integer) to HH:MM formatted string
    hours = minutes // 60
    mins = minutes % 60
    return "{:02d}:{:02d}".format(hours, mins)

# Define working hours and meeting duration (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Billy's preference: avoid meetings after 15:00.
latest_meeting_end = time_to_minutes("15:00")

# Define each participant's busy intervals on Monday in (start, end) format (in minutes)
# (Note: times are in 24-hour HH:MM format.)
schedules = {
    "Raymond": [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("15:00", "15:30")],
    "Billy":   [("10:00", "10:30"), ("12:00", "13:00"), ("16:30", "17:00")],
    "Donald":  [("09:00", "09:30"), ("10:00", "11:00"), ("12:00", "13:00"), ("14:00", "14:30"), ("16:00", "17:00")]
}

# Convert schedules to minutes
for person, intervals in schedules.items():
    schedules[person] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

# Function to compute free intervals from busy intervals within working hours
def compute_free_intervals(busy_intervals, start, end):
    free = []
    # sort the busy intervals
    busy_intervals.sort()
    current = start
    for b_start, b_end in busy_intervals:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

# Compute free intervals for each participant
free_times = {}
for person, busy in schedules.items():
    free_times[person] = compute_free_intervals(busy, work_start, work_end)

# Function to intersect two lists of intervals
def intersect_intervals(ints1, ints2):
    i, j = 0, 0
    result = []
    while i < len(ints1) and j < len(ints2):
        start1, end1 = ints1[i]
        start2, end2 = ints2[j]
        inter_start = max(start1, start2)
        inter_end = min(end1, end2)
        if inter_start < inter_end:
            result.append((inter_start, inter_end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Intersect free intervals for all participants
common_free = free_times["Raymond"]
for person in ["Billy", "Donald"]:
    common_free = intersect_intervals(common_free, free_times[person])

# From the common free intervals, choose an interval that fits the meeting duration
# and satisfies Billy's preference that the meeting ends by 15:00.
proposed_meeting = None
for start, end in common_free:
    # Adjust end if exceeding Billy's preference (meeting must finish by 15:00)
    latest_possible_end = min(end, latest_meeting_end)
    if latest_possible_end - start >= meeting_duration:
        proposed_meeting = (start, start + meeting_duration)
        break

if proposed_meeting:
    start_time, end_time = proposed_meeting
    meeting_time_str = f"{minutes_to_time(start_time)}:{minutes_to_time(end_time)}"
    day = "Monday"
    print(f"{meeting_time_str} {day}")
else:
    print("No suitable meeting time found.")