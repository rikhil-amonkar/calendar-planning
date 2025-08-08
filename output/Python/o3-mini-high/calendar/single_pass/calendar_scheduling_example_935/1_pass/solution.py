from datetime import datetime, timedelta

# Helper functions to convert between "HH:MM" strings and minutes since midnight.
def time_to_minutes(t):
    """Convert a string HH:MM to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM formatted string."""
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals):
    """Merge overlapping or contiguous intervals.
       Each interval is a tuple (start, end) in minutes.
    """
    if not intervals:
        return []
    # Sort intervals by start time.
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        # If current interval overlaps or touches the last, merge them.
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_slot(busy_intervals, work_start, work_end, duration):
    """Given merged busy intervals and working hours, return the earliest free slot (start, end) 
       that is at least 'duration' minutes long.
    """
    free_slots = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            if start - current >= duration:
                free_slots.append((current, start))
        current = max(current, end)
    if work_end - current >= duration:
        free_slots.append((current, work_end))
    # Return the earliest free slot that fits.
    if free_slots:
        return free_slots[0]
    return None

# Define the schedules for both participants.
schedules = {
    "Monday": {
         "Terry": [("10:30", "11:00"), ("12:30", "14:00"), ("15:00", "17:00")],
         "Frances": [("9:30", "11:00"), ("11:30", "13:00"), ("14:00", "14:30"), ("15:00", "16:00")]
    },
    "Tuesday": {
         "Terry": [("9:30", "10:00"), ("10:30", "11:00"), ("14:00", "14:30"), ("16:00", "16:30")],
         "Frances": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "12:00"), ("13:00", "14:30"), ("15:30", "16:30")]
    },
    "Wednesday": {
         "Terry": [("9:30", "10:30"), ("11:00", "12:00"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
         "Frances": [("9:30", "10:00"), ("10:30", "11:00"), ("11:30", "16:00"), ("16:30", "17:00")]
    },
    "Thursday": {
         "Terry": [("9:30", "10:00"), ("12:00", "12:30"), ("13:00", "14:30"), ("16:00", "16:30")],
         "Frances": [("11:00", "12:30"), ("14:30", "17:00")]
    },
    "Friday": {
         "Terry": [("9:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")],
         "Frances": [("9:30", "10:30"), ("11:00", "12:30"), ("13:00", "16:00"), ("16:30", "17:00")]
    }
}

# Meeting and work configuration.
meeting_duration = 30  # duration in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Preferred day order taking into account Frances' preference to avoid Tuesday.
preferred_days = ["Monday", "Wednesday", "Thursday", "Friday", "Tuesday"]

# Search for the earliest available slot among the preferred days.
found_slot = None
meeting_day = None
meeting_start = None
meeting_end = None

for day in preferred_days:
    # If the day is not in our schedule dictionary, assume no meetings scheduled for that day.
    day_schedule = schedules.get(day, {})
    
    # Gather all busy intervals for the day from both participants.
    busy_intervals = []
    for person, intervals in day_schedule.items():
        for interval in intervals:
            start = time_to_minutes(interval[0])
            end = time_to_minutes(interval[1])
            busy_intervals.append((start, end))
    
    # Merge busy intervals.
    merged_busy = merge_intervals(busy_intervals)
    
    # Find the earliest free slot that can fit the meeting.
    slot = find_free_slot(merged_busy, work_start, work_end, meeting_duration)
    if slot:
        meeting_day = day
        meeting_start, slot_end = slot
        meeting_end = meeting_start + meeting_duration
        found_slot = True
        break

if found_slot:
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output in the format: Day {HH:MM:HH:MM}
    print(f"{meeting_day} {{{start_str}:{end_str}}}")
else:
    print("No available slot found.")