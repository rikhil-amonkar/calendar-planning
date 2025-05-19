from datetime import time, datetime, timedelta

# Define a helper function to convert time string to minutes since midnight
def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Define a helper function to convert minutes since midnight to time string in HH:MM format
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define working hours (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Meeting duration in minutes
meeting_duration = 60

# Define busy slots for each participant as tuples (start, end) in minutes
busy_slots = {
    "Olivia": [("12:30", "13:30"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Anna": [],  # Free full day
    "Virginia": [("09:00", "10:00"), ("11:30", "16:00"), ("16:30", "17:00")],
    "Paul": [("09:00", "09:30"), ("11:00", "11:30"), ("13:00", "14:00"), ("14:30", "16:00"), ("16:30", "17:00")]
}

# Function to determine free intervals from busy intervals within work hours
def get_free_intervals(busy_periods):
    # sort busy periods by start time (in minutes)
    busy_periods_minutes = sorted([(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_periods])
    free_intervals = []
    current_start = work_start

    for start, end in busy_periods_minutes:
        if start > current_start:
            free_intervals.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    return free_intervals

# Get free intervals for each participant
free_intervals = {person: get_free_intervals(busy_slots[person]) for person in busy_slots}

# A function to get the intersection between two lists of intervals
def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        # calculate the intersection of intervals1[i] and intervals2[j]
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        # move forward in whichever interval ends earlier
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

# Find common free intervals among all participants
participants = list(busy_slots.keys())
common_free = free_intervals[participants[0]]
for person in participants[1:]:
    common_free = intersect_intervals(common_free, free_intervals[person])

# Now find a common free interval that can hold the meeting duration
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

# Define the day of the week
meeting_day = "Monday"

if meeting_slot:
    start_time_str = minutes_to_time(meeting_slot[0])
    end_time_str = minutes_to_time(meeting_slot[1])
    print(f"{meeting_day} {start_time_str}:{end_time_str}")
else:
    print("No available meeting slot found.")