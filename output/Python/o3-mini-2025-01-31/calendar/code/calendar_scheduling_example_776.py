from datetime import timedelta, datetime

# Helper functions to convert time strings and minutes.
def time_to_minutes(time_str):
    """Convert a time string 'HH:MM' to minutes since midnight."""
    t = datetime.strptime(time_str, "%H:%M")
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    """Convert minutes since midnight to a time string 'HH:MM'."""
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals. Each interval is (start, end) in minutes."""
    if not intervals:
        return []
    intervals = sorted(intervals, key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_intervals(busy_intervals, work_start, work_end):
    """Given busy time intervals (in minutes) during the work day, return free intervals."""
    free_intervals = []
    # Start with the beginning of the work day.
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

# Meeting duration in minutes
meeting_duration = 30

# Workday start/end in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# John's schedule:
# John has no meetings, but on Monday he prefers NOT to have meetings after 14:30.
# We'll treat that as an additional constraint: for Monday, the meeting must end by 14:30.
john_monday_limit = time_to_minutes("14:30")

# Jennifer's existing schedules per day with busy intervals (times in minutes)
schedules = {
    "Monday": [
        (time_to_minutes("09:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ],
    "Tuesday": [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("17:00"))
    ],
    "Wednesday": [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Candidate days in order of preference: Monday, Tuesday, Wednesday
candidate_days = ["Monday", "Tuesday", "Wednesday"]

proposed_time = None
proposed_day = None

for day in candidate_days:
    # Merge Jennifer's busy intervals for the day
    busy = merge_intervals(schedules.get(day, []))
    
    # For Monday, if John's condition applies, we restrict the effective work_end to 14:30.
    effective_work_end = work_end
    if day == "Monday":
        effective_work_end = min(work_end, john_monday_limit)
        
    # Find free intervals within the effective work hours
    free_intervals = find_free_intervals(busy, work_start, effective_work_end)
    
    # Search for a free interval that can accommodate meeting_duration minutes.
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            proposed_day = day
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            proposed_time = (meeting_start, meeting_end)
            break
    if proposed_time is not None:
        break

if proposed_time and proposed_day:
    start_time_str = minutes_to_time(proposed_time[0])
    end_time_str = minutes_to_time(proposed_time[1])
    # Output format: HH:MM:HH:MM and day of the week.
    print(f"{start_time_str}:{end_time_str} on {proposed_day}")
else:
    print("No suitable time found.")