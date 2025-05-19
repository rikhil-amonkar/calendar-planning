from datetime import datetime, timedelta

# Utility functions to convert between "HH:MM" and minutes past midnight
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m//60:02}:{m%60:02}"

# Function to get free intervals from busy intervals within work hours
def get_free_intervals(busy_intervals, work_start, work_end):
    free_intervals = []
    # Start with the beginning of work hours
    current = work_start
    for start, end in sorted(busy_intervals):
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

# Function to intersect two lists of intervals
def intersect_intervals(intervals1, intervals2):
    result = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if end - start >= 0:
                result.append((start, end))
    # Merge overlapping intervals if needed (not necessary in this simple use-case)
    return result

# Meeting information
meeting_duration = 30  # minutes
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Schedules for each participant
# Times are given as tuples (start, end) in "HH:MM" strings
schedules = {
    "Ryan": {
        "Monday": [("09:30", "10:00"), ("11:00", "12:00"), ("13:00", "13:30"), ("15:30", "16:00")],
        "Tuesday": [("11:30", "12:30"), ("15:30", "16:00")],
        "Wednesday": [("12:00", "13:00"), ("15:30", "16:00"), ("16:30", "17:00")]
    },
    "Adam": {
        "Monday": [("09:00", "10:30"), ("11:00", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")],
        "Tuesday": [("09:00", "10:00"), ("10:30", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("09:00", "9:30"), ("10:00", "11:00"), ("11:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")]
    }
}

# Additional constraints:
# - Ryan cannot meet on Wednesday.
# - Adam would like to avoid more meetings on Monday before 14:30.
#   (We interpret this as preferring a meeting time on Monday not starting before 14:30,
#    if a solution is available on another day, we'll choose that.)

# Candidate days and apply hard constraints
candidate_days = ["Monday", "Tuesday", "Wednesday"]
# Remove Wednesday because Ryan cannot meet on Wednesday.
candidate_days = [day for day in candidate_days if day != "Wednesday"]

def convert_schedule(day, person):
    """Converts schedule time intervals to minutes for a given day."""
    busy = []
    for start, end in schedules[person].get(day, []):
        busy.append((time_to_minutes(start), time_to_minutes(end)))
    return busy

meeting_slot = None
meeting_day = None

# We try candidate days. We'll prefer days that satisfy preferences.
# First check Tuesday, then Monday. (Because Adam prefers to avoid Monday before 14:30.)
preferred_order = ["Tuesday", "Monday"]

for day in preferred_order:
    ryan_busy = convert_schedule(day, "Ryan")
    adam_busy = convert_schedule(day, "Adam")
    
    ryan_free = get_free_intervals(ryan_busy, work_start, work_end)
    adam_free = get_free_intervals(adam_busy, work_start, work_end)
    
    # Intersect free intervals between Ryan and Adam
    common_free = intersect_intervals(ryan_free, adam_free)
    
    # Sort common free intervals by start time
    common_free.sort(key=lambda x: x[0])
    
    # Try to find a common interval that can accommodate meeting_duration 
    for start, end in common_free:
        if end - start >= meeting_duration:
            # For Monday, check Adam's preference: avoid meetings before 14:30
            if day == "Monday" and start < time_to_minutes("14:30"):
                # Try to adjust start time if possible within the interval
                adjusted_start = max(start, time_to_minutes("14:30"))
                if end - adjusted_start >= meeting_duration:
                    start = adjusted_start
                else:
                    # Skip this interval since it doesn't satisfy Adam's preference.
                    continue
            meeting_slot = (start, start + meeting_duration)
            meeting_day = day
            break
    if meeting_slot:
        break

if meeting_slot:
    start_str = minutes_to_time(meeting_slot[0])
    end_str = minutes_to_time(meeting_slot[1])
    print(f"{meeting_day}: {start_str}:{end_str}")
else:
    print("No suitable meeting slot found.")