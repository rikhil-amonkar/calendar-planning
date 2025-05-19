from datetime import datetime, timedelta

# Utility functions to convert time strings to minutes and back.
def time_to_minutes(time_str):
    # time_str format "HH:MM"
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Working hours (9:00 to 17:00) as minutes
WORK_START = time_to_minutes("09:00")
WORK_END   = time_to_minutes("17:00")
MEETING_DURATION = 30  # meeting duration in minutes

# Schedules for each participant.
# Each schedule is a dict with keys as days and values as list of busy intervals.
# Each busy interval is represented as a tuple (start, end) in minutes.
daniel_busy = {
    "Monday":    [("09:30", "10:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Tuesday":   [("11:00", "12:00"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Wednesday": [("09:00", "10:00"), ("14:00", "14:30")],
    "Thursday":  [("10:30", "11:00"), ("12:00", "13:00"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Friday":    [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:30", "17:00")]
}
bradley_busy = {
    "Monday":    [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("14:00", "15:00")],
    "Tuesday":   [("10:30", "11:00"), ("12:00", "13:00"), ("13:30", "14:00"), ("15:30", "16:30")],
    "Wednesday": [("09:00", "10:00"), ("11:00", "13:00"), ("13:30", "14:00"), ("14:30", "17:00")],
    "Thursday":  [("09:00", "12:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Friday":    [("09:00", "09:30"), ("10:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:30", "16:30")]
}

# Preferences:
# Daniel: would rather not meet on Wednesday or Thursday.
# Bradley: does not want to meet on Monday, not before 12:00 on Tuesday, and not on Friday.
# Allowed days given these preferences: Only Tuesday is acceptable.
allowed_days = ["Tuesday"]

# Function to compute free intervals given a list of busy intervals on a day.
def compute_free_intervals(busy_times):
    # Convert busy intervals into minutes
    intervals = []
    for start, end in busy_times:
        intervals.append((time_to_minutes(start), time_to_minutes(end)))
    # Sort intervals by start time
    intervals.sort()
    free_intervals = []
    current_start = WORK_START
    for bstart, bend in intervals:
        if bstart > current_start:
            free_intervals.append((current_start, bstart))
        current_start = max(current_start, bend)
    if current_start < WORK_END:
        free_intervals.append((current_start, WORK_END))
    return free_intervals

# Function to get the intersection of two lists of intervals.
def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap interval
        start_overlap = max(start1, start2)
        end_overlap   = min(end1, end2)
        if start_overlap + MEETING_DURATION <= end_overlap:
            intersections.append((start_overlap, end_overlap))
        # Move to the next interval in the list with the earlier end time
        if end1 <= end2:
            i += 1
        else:
            j += 1
    return intersections

proposed_meeting = None
proposed_day = None

for day in allowed_days:
    # Compute free intervals for Daniel and Bradley on this day.
    daniel_free = compute_free_intervals(daniel_busy.get(day, []))
    bradley_free = compute_free_intervals(bradley_busy.get(day, []))
    
    # Apply Bradley's additional constraint for Tuesday:
    # "Tuesday before 12:00" is not allowed. So adjust Bradley's free intervals if day is Tuesday.
    if day == "Tuesday":
        adjusted = []
        for start, end in bradley_free:
            if end <= time_to_minutes("12:00"):
                # skip intervals finishing before 12:00
                continue
            # Ensure the interval starts at least at 12:00
            adjusted.append((max(start, time_to_minutes("12:00")), end))
        bradley_free = adjusted

    # Find overlapping free intervals.
    common_free = intersect_intervals(daniel_free, bradley_free)
    # Check if any interval is long enough for the meeting
    for start, end in common_free:
        if end - start >= MEETING_DURATION:
            proposed_meeting = (start, start + MEETING_DURATION)
            proposed_day = day
            break
    if proposed_meeting:
        break

if proposed_meeting and proposed_day:
    meeting_start = minutes_to_time(proposed_meeting[0])
    meeting_end   = minutes_to_time(proposed_meeting[1])
    print(f"{proposed_day} {meeting_start}:{meeting_end}")
else:
    print("No available meeting slot found within the constraints.")