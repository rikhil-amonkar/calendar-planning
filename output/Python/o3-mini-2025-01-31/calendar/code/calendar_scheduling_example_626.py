from datetime import time, datetime, timedelta

# Helper function to convert HH:MM string to minutes from midnight.
def time_to_minutes(t_str):
    t = datetime.strptime(t_str, "%H:%M")
    return t.hour * 60 + t.minute

# Helper function to convert minutes to HH:MM format string.
def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Define the working hours in minutes (09:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Busy intervals for each participant per day (in minutes from midnight)
# Format: { day: { participant: [(start, end), ...] } }

schedules = {
    "Monday": {
        "Patricia": [
            (time_to_minutes("10:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("16:30")),
        ],
        "Jesse": [
            (time_to_minutes("09:00"), time_to_minutes("17:00")),  # entire day busy
        ],
    },
    "Tuesday": {
        "Patricia": [
            (time_to_minutes("10:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:00"), time_to_minutes("12:00")),
            (time_to_minutes("14:00"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00")),
        ],
        "Jesse": [
            (time_to_minutes("11:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("14:00")),
            (time_to_minutes("14:30"), time_to_minutes("15:00")),
            (time_to_minutes("15:30"), time_to_minutes("17:00")),
        ],
    }
}

# Function to compute free intervals given busy intervals over a working period.
def compute_free_intervals(busy_intervals, start=work_start, end=work_end):
    # Sort intervals by start time.
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current_start = start
    for b_start, b_end in busy_intervals:
        if current_start < b_start:
            free_intervals.append((current_start, b_start))
        current_start = max(current_start, b_end)
    if current_start < end:
        free_intervals.append((current_start, end))
    return free_intervals

# Find common free intervals between two participants on a given day.
def find_common_free_intervals(day, participants):
    # Compute free intervals for each participant.
    free = {}
    for person in participants:
        busy = schedules[day].get(person, [])
        free[person] = compute_free_intervals(busy)
    
    # Intersect free intervals across participants.
    # We'll use a two interval list intersection method.
    def intersect_intervals(intervals1, intervals2):
        i, j = 0, 0
        common = []
        while i < len(intervals1) and j < len(intervals2):
            start1, end1 = intervals1[i]
            start2, end2 = intervals2[j]
            # Find overlap.
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            if overlap_start < overlap_end:
                common.append((overlap_start, overlap_end))
            # Move to the next interval in the list which ends first.
            if end1 <= end2:
                i += 1
            else:
                j += 1
        return common

    # Start with the free intervals of the first participant.
    common_free = free[participants[0]]
    # Intersect with the remaining participant's free intervals.
    for person in participants[1:]:
        common_free = intersect_intervals(common_free, free[person])
    return common_free

# Try each day (Monday and Tuesday) and pick the first slot that can accommodate a meeting of meeting_duration minutes.
chosen_day = None
chosen_interval = None

for day in ["Monday", "Tuesday"]:
    # We need the meeting for both Patricia and Jesse.
    common_free = find_common_free_intervals(day, ["Patricia", "Jesse"])
    for interval in common_free:
        start, end = interval
        if end - start >= meeting_duration:
            chosen_day = day
            chosen_interval = (start, start + meeting_duration)
            break
    if chosen_day:
        break

if chosen_day and chosen_interval:
    meeting_start = minutes_to_time(chosen_interval[0])
    meeting_end = minutes_to_time(chosen_interval[1])
    print(f"{chosen_day} {meeting_start}:{meeting_end}")
else:
    print("No common free slot found.")