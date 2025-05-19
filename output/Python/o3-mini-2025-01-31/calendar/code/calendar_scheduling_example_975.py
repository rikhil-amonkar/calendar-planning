from datetime import datetime, timedelta

# Helper function: convert HH:MM string to minutes since midnight
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Helper function: convert minutes since midnight to HH:MM format
def minutes_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

# Work day boundaries (in minutes since midnight)
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Participant schedules represented as dictionary mapping day -> list of (start, end) in minutes
# Nicole's schedule
nicole_schedule = {
    "Tuesday": [(time_to_minutes("16:00"), time_to_minutes("16:30"))],
    "Wednesday": [(time_to_minutes("15:00"), time_to_minutes("15:30"))],
    "Friday": [(time_to_minutes("12:00"), time_to_minutes("12:30")),
               (time_to_minutes("15:30"), time_to_minutes("16:00"))]
}

# Daniel's schedule
daniel_schedule = {
    "Monday": [(time_to_minutes("09:00"), time_to_minutes("12:30")),
               (time_to_minutes("13:00"), time_to_minutes("13:30")),
               (time_to_minutes("14:00"), time_to_minutes("16:30"))],
    "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("10:30")),
                (time_to_minutes("11:30"), time_to_minutes("12:30")),
                (time_to_minutes("13:00"), time_to_minutes("13:30")),
                (time_to_minutes("15:00"), time_to_minutes("16:00")),
                (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    "Wednesday": [(time_to_minutes("09:00"), time_to_minutes("10:00")),
                  (time_to_minutes("11:00"), time_to_minutes("12:30")),
                  (time_to_minutes("13:00"), time_to_minutes("13:30")),
                  (time_to_minutes("14:00"), time_to_minutes("14:30")),
                  (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    "Thursday": [(time_to_minutes("11:00"), time_to_minutes("12:00")),
                 (time_to_minutes("13:00"), time_to_minutes("14:00")),
                 (time_to_minutes("15:00"), time_to_minutes("15:30"))],
    "Friday": [(time_to_minutes("10:00"), time_to_minutes("11:00")),
               (time_to_minutes("11:30"), time_to_minutes("12:00")),
               (time_to_minutes("12:30"), time_to_minutes("14:30")),
               (time_to_minutes("15:00"), time_to_minutes("15:30")),
               (time_to_minutes("16:00"), time_to_minutes("16:30"))]
}

# List of days in order
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

def merge_intervals(intervals):
    """Merge overlapping intervals."
    """
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_interval(busy_intervals, day_start, day_end, duration):
    """
    Given busy_intervals (merged and sorted), find the earliest free interval
    of at least 'duration' minutes between day_start and day_end.
    Returns the start time if found, else None.
    """
    # Check before the first busy interval
    if not busy_intervals:
        if day_end - day_start >= duration:
            return day_start
        else:
            return None

    if busy_intervals[0][0] - day_start >= duration:
        return day_start

    # Check gaps between busy intervals
    for i in range(len(busy_intervals) - 1):
        end_current = busy_intervals[i][1]
        start_next = busy_intervals[i+1][0]
        if start_next - end_current >= duration:
            return end_current

    # Check after the last busy interval
    if day_end - busy_intervals[-1][1] >= duration:
        return busy_intervals[-1][1]

    return None

# Find earliest meeting time across days
scheduled_day = None
meeting_start = None

for day in days:
    # Gather busy intervals for both participants on this day
    intervals = []
    if day in nicole_schedule:
        intervals.extend(nicole_schedule[day])
    if day in daniel_schedule:
        intervals.extend(daniel_schedule[day])
    # Merge intervals to handle any overlapping intervals
    busy = merge_intervals(intervals)
    # Find a free time slot on this day
    free_start = find_free_interval(busy, work_start, work_end, meeting_duration)
    if free_start is not None:
        scheduled_day = day
        meeting_start = free_start
        break  # found the earliest day and time

if scheduled_day is not None:
    meeting_end = meeting_start + meeting_duration
    # Format output as HH:MM:HH:MM and day
    meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    print(f"Meeting scheduled on {scheduled_day} at {meeting_time_str}")
else:
    print("No available time slot found for the meeting.")