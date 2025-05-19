from datetime import timedelta, datetime

# Define working day start and end times (using datetime objects for ease)
WORK_DAY = "09:00", "17:00"
meeting_duration = timedelta(minutes=30)
day_of_week = "Monday"

# Convert time strings to datetime objects (the specific date is arbitrary, we use a dummy date)
def to_datetime(time_str):
    return datetime.strptime(time_str, "%H:%M")

work_start = to_datetime(WORK_DAY[0])
work_end   = to_datetime(WORK_DAY[1])

# Each participant's busy intervals (as tuples of start and end times)
# Times are given as strings in "HH:MM" format
busy_times = {
    "Ronald": [],  # Wide open
    "Stephen": [("10:00", "10:30"), ("12:00", "12:30")],
    "Brittany": [("11:00", "11:30"), ("13:30", "14:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Dorothy": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "12:30"), ("13:00", "15:00"), ("15:30", "17:00")],
    "Rebecca": [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "17:00")],
    "Jordan": [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:00"), ("13:00", "15:00"), ("15:30", "16:30")]
}

# Helper function: Convert an interval from strings to datetime objects
def parse_interval(interval):
    start, end = interval
    return to_datetime(start), to_datetime(end)

# For a given list of busy intervals (as datetime tuples), compute free intervals within the work day
def compute_free_intervals(busy_list):
    # First, sort busy intervals by start time
    busy_list = sorted([parse_interval(interval) for interval in busy_list], key=lambda x: x[0])
    free = []
    current = work_start
    for bstart, bend in busy_list:
        if current < bstart:
            free.append((current, bstart))
        # Move current pointer to the later of current or bend
        if bend > current:
            current = bend
    if current < work_end:
        free.append((current, work_end))
    return free

# Compute free intervals for each participant
free_intervals = {}
for participant, busy in busy_times.items():
    free_intervals[participant] = compute_free_intervals(busy)

# Function to intersect two lists of intervals
def intersect_intervals(list1, list2):
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find overlap
        latest_start = max(start1, start2)
        earliest_end = min(end1, end2)
        if latest_start < earliest_end:
            result.append((latest_start, earliest_end))
        # Move to the next interval in the list with the earlier end time
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Intersect free intervals for all participants
all_free = list(free_intervals.values())[0]
for intervals in list(free_intervals.values())[1:]:
    all_free = intersect_intervals(all_free, intervals)

# Find the first interval that can accommodate the meeting duration
proposed_time = None
for start, end in all_free:
    if end - start >= meeting_duration:
        proposed_time = (start, start + meeting_duration)
        break

if proposed_time:
    start_time, end_time = proposed_time
    # Format the output in HH:MM:HH:MM
    output = f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}"
    print(f"Day: {day_of_week}, Meeting Time: {output}")
else:
    print("No suitable time slot found.")
    
# In this specific case, the meeting is scheduled on Monday from 12:30 to 13:00.