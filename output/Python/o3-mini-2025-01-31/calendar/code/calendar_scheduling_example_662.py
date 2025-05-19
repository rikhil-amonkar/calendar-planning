from datetime import time, timedelta, datetime

def time_to_minutes(t):
    """Convert a time string HH:MM to minutes from 00:00."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time_str(minutes):
    """Convert minutes (from 00:00) back to HH:MM string format."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def invert_busy(busy, work_start, work_end):
    """
    Given a list of busy intervals (as tuples of start and end in minutes)
    within the working period [work_start, work_end], return a list of free intervals.
    """
    free = []
    current = work_start
    for interval in sorted(busy):
        start, end = interval
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Return the intersection of two lists of intervals."""
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

def find_slot(free_intervals, duration):
    """Find a slot of at least 'duration' minutes in the list of intervals."""
    for start, end in free_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

# Define working hours (in minutes from midnight)
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")
meeting_duration = 60  # minutes

# Define busy schedules for each person in minutes
# Format: { 'Day': [(start, end), ...] }
gary_busy = {
    "Monday": [(time_to_minutes("09:30"), time_to_minutes("10:00")),
               (time_to_minutes("11:00"), time_to_minutes("13:00")),
               (time_to_minutes("14:00"), time_to_minutes("14:30")),
               (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                (time_to_minutes("10:30"), time_to_minutes("11:00")),
                (time_to_minutes("14:30"), time_to_minutes("16:00"))]
}

david_busy = {
    "Monday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
               (time_to_minutes("10:00"), time_to_minutes("13:00")),
               (time_to_minutes("14:30"), time_to_minutes("16:30"))],
    "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                (time_to_minutes("10:00"), time_to_minutes("10:30")),
                (time_to_minutes("11:00"), time_to_minutes("12:30")),
                (time_to_minutes("13:00"), time_to_minutes("14:30")),
                (time_to_minutes("15:00"), time_to_minutes("16:00")),
                (time_to_minutes("16:30"), time_to_minutes("17:00"))]
}

# We search for a meeting slot that works for all participants.
days = ["Monday", "Tuesday"]
meeting_slot = None
meeting_day = None

for day in days:
    # Calculate free intervals for each participant on this day.
    gary_free = invert_busy(gary_busy[day], work_start, work_end)
    david_free = invert_busy(david_busy[day], work_start, work_end)
    
    # Find common free intervals by intersecting their free intervals.
    common_free = intersect_intervals(gary_free, david_free)
    
    # Check if any common free interval can accommodate the meeting duration.
    slot = find_slot(common_free, meeting_duration)
    if slot:
        meeting_slot = slot
        meeting_day = day
        break

if meeting_slot:
    start_time_str = minutes_to_time_str(meeting_slot[0])
    end_time_str = minutes_to_time_str(meeting_slot[1])
    print(f"{meeting_day} {start_time_str}:{end_time_str}")
else:
    print("No available meeting slot found.")