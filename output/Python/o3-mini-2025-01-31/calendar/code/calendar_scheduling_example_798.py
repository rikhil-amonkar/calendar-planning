from datetime import datetime, timedelta

# Meeting duration in minutes
MEETING_DURATION = 30

# Work hours (in minutes from midnight)
WORK_START = 9 * 60   # 9:00 AM in minutes
WORK_END = 17 * 60    # 17:00 (5:00 PM) in minutes

# Helper functions
def time_to_minutes(time_str):
    """Convert a time string 'HH:MM' to minutes since midnight."""
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    """Convert minutes since midnight to a time string 'HH:MM'."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def invert_busy(busy_intervals):
    """
    Given a list of busy intervals (start, end) in minutes,
    return a list of free intervals within the work hours.
    """
    free_intervals = []
    current_start = WORK_START
    # sort the busy intervals by start time
    busy_intervals.sort(key=lambda interval: interval[0])
    for bstart, bend in busy_intervals:
        if current_start < bstart:
            free_intervals.append((current_start, bstart))
        current_start = max(current_start, bend)
    if current_start < WORK_END:
        free_intervals.append((current_start, WORK_END))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, return the intersection intervals.
    """
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # find overlapping interval
        start = max(start1, start2)
        end = min(end1, end2)
        if start + MEETING_DURATION <= end:
            intersections.append((start, end))
        # move the pointer which ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Participant busy schedules in minutes from midnight
# Format: { day: [ (busy_start, busy_end), ... ] }
nancy_busy = {
    "Monday": [("10:00", "10:30"), ("11:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
    "Tuesday": [("9:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00")],
    "Wednesday": [("10:00", "11:30"), ("13:30", "16:00")]
}

jose_busy = {
    "Monday": [("09:00", "17:00")],
    "Tuesday": [("09:00", "17:00")],
    "Wednesday": [("09:00", "09:30"), ("10:00", "12:30"), ("13:30", "14:30"), ("15:00", "17:00")]
}

# Convert the time strings to minutes
for day in nancy_busy:
    nancy_busy[day] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in nancy_busy[day]]
for day in jose_busy:
    jose_busy[day] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in jose_busy[day]]

days = ["Monday", "Tuesday", "Wednesday"]

# Scan days in order to find the earliest available meeting slot
found_slot = False
meeting_day = None
meeting_start = None

for day in days:
    # Calculate free intervals for each participant, given the work hours
    nancy_free = invert_busy(nancy_busy.get(day, []))
    jose_free = invert_busy(jose_busy.get(day, []))
    
    # Find intersections between free time slots
    common_free = intersect_intervals(nancy_free, jose_free)
    
    # Look for the earliest common interval that can accommodate the meeting duration
    if common_free:
        # Take the first interval's start time that fits the meeting duration
        for interval in common_free:
            start, end = interval
            if start + MEETING_DURATION <= end:
                meeting_day = day
                meeting_start = start
                found_slot = True
                break
    if found_slot:
        break

if found_slot:
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_start + MEETING_DURATION)
    # Output in the required format: day and time range HH:MM:HH:MM
    print(f"{meeting_day}, {start_time_str}:{end_time_str}")
else:
    print("No available time slot found.")