from datetime import datetime, timedelta

# Helper functions to convert between "HH:MM" strings and minutes since midnight
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    return f"{minutes//60:02d}:{minutes%60:02d}"

# Define the work day boundaries for Monday in minutes
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Busy intervals for each participant (start, end) in HH:MM format
schedules = {
    "Gregory": [("09:00", "10:00"), ("10:30", "11:30"), ("12:30", "13:00"), ("13:30", "14:00")],
    "Natalie": [],  # Natalie is free the entire day
    "Christine": [("09:00", "11:30"), ("13:30", "17:00")],
    "Vincent": [("09:00", "09:30"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")]
}

# Convert busy intervals to minutes
def convert_schedule(busy_intervals):
    return [(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_intervals]

converted_schedules = {person: convert_schedule(busy)
                       for person, busy in schedules.items()}

# Given a list of busy intervals for a participant and the work day boundaries,
# compute the free intervals
def get_free_intervals(busy_intervals, start=work_start, end=work_end):
    # Sort intervals
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current_start = start

    for b_start, b_end in busy_intervals:
        if b_start > current_start:
            free_intervals.append((current_start, b_start))
        current_start = max(current_start, b_end)
    if current_start < end:
        free_intervals.append((current_start, end))
    return free_intervals

# Calculate free intervals for each person
free_times = {person: get_free_intervals(busy)
              for person, busy in converted_schedules.items()}

# Function to compute intersection of two interval lists
def intersect_intervals(list1, list2):
    i, j = 0, 0
    intersection = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find the intersection of these two intervals
        start_int = max(start1, start2)
        end_int = min(end1, end2)
        if start_int < end_int:
            intersection.append((start_int, end_int))
        # Move on from the interval that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Compute the common free intervals for all participants
participants = list(free_times.keys())
common_free = free_times[participants[0]]
for person in participants[1:]:
    common_free = intersect_intervals(common_free, free_times[person])

# Now, from the common free intervals, pick the first interval
# that is at least meeting_duration minutes long.
meeting_time = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_time = (start, start + meeting_duration)
        break

if meeting_time:
    start_str = minutes_to_time(meeting_time[0])
    end_str = minutes_to_time(meeting_time[1])
    day = "Monday"
    print(f"{day} {start_str}:{end_str}")
else:
    print("No available time slot found.")