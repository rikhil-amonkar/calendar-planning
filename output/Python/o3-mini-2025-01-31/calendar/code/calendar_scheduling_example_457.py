def to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_time_str(minutes):
    """Convert minutes since midnight to HH:MM format."""
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

# Define workday start and end in minutes
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes

# Busy times for each participant on Monday as (start, end) in minutes
schedules = {
    "Andrea": [("09:30", "10:30"), ("13:30", "14:30")],
    "Ruth":   [("12:30", "13:00"), ("15:00", "15:30")],
    "Steven": [("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
               ("13:30", "14:00"), ("15:00", "16:00")],
    "Grace":  [],  # free whole day
    "Kyle":   [("09:00", "09:30"), ("10:30", "12:00"), ("12:30", "13:00"),
               ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Elijah": [("09:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:00"),
               ("15:30", "16:00"), ("16:30", "17:00")],
    "Lori":   [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "13:30"),
               ("14:00", "16:00"), ("16:30", "17:00")]
}

def get_free_intervals(busy_intervals, day_start, day_end):
    """Given a list of busy intervals in minutes, return free intervals in the day."""
    # sort busy intervals by start time
    busy_intervals = sorted([(to_minutes(s), to_minutes(e)) for s, e in busy_intervals])
    free_intervals = []
    current_start = day_start
    for start, end in busy_intervals:
        if current_start < start:
            free_intervals.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < day_end:
        free_intervals.append((current_start, day_end))
    return free_intervals

# Calculate free intervals for each participant
free_schedules = {}
for person, busy_times in schedules.items():
    free_schedules[person] = get_free_intervals(busy_times, work_start, work_end)

# Function to find intersection of two lists of intervals
def intersect_intervals(intervals1, intervals2):
    result = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        # find the max start and min end
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:  # valid intersection
            result.append((start, end))
        # move on from the interval with the smallest end time
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

# Intersect free intervals among all participants
common_free = [(work_start, work_end)]
for person, free_int in free_schedules.items():
    common_free = intersect_intervals(common_free, free_int)
    # If at any point there is no common free time, you can break (but guaranteed a solution exists)
    if not common_free:
        break

# Find a common interval that can fit the meeting duration
meeting_time = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_time = (start, start + meeting_duration)
        break

if meeting_time:
    meeting_start_str = to_time_str(meeting_time[0])
    meeting_end_str = to_time_str(meeting_time[1])
    day = "Monday"
    print(f"{day} {meeting_start_str}:{meeting_end_str}")
else:
    print("No common meeting time found.")