def time_to_minutes(t_str):
    # Converts a time string "HH:MM" to total minutes since midnight.
    hours, minutes = map(int, t_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Converts total minutes since midnight back to "HH:MM" formatted string.
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs:02d}:{mins:02d}"

def get_free_intervals(working_start, working_end, busy_intervals):
    # Given the working period and a list of busy intervals (as tuples in minutes),
    # return the list of free intervals as (start, end) in minutes.
    free = []
    current = working_start
    # Sort busy intervals by start time.
    for start, end in sorted(busy_intervals):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < working_end:
        free.append((current, working_end))
    return free

def intersect_intervals(intervals1, intervals2, meeting_duration):
    # Find intersections between two lists of intervals.
    intersections = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if end - start >= meeting_duration:
                intersections.append((start, end))
    return intersections

# Define work hours: 9:00 to 17:00
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
MEETING_DURATION = 30  # minutes

# Define busy schedules for each participant on each day.
schedules = {
    "Nicole": {
        "Monday": [("09:00", "09:30"), ("13:00", "13:30"), ("14:30", "15:30")],
        "Tuesday": [("09:00", "09:30"), ("11:30", "13:30"), ("14:30", "15:30")],
        "Wednesday": [("10:00", "11:00"), ("12:30", "15:00"), ("16:00", "17:00")]
    },
    "Ruth": {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:00", "17:00")],
        "Wednesday": [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
                      ("13:30", "15:30"), ("16:00", "16:30")]
    }
}

# Ruth's extra preference: on Wednesday, do not meet after 13:30.
def apply_preference(free_intervals, day):
    if day == "Wednesday":
        limit = time_to_minutes("13:30")
        adjusted = []
        for start, end in free_intervals:
            # Only consider the part before 13:30
            if start < limit:
                adjusted.append((start, min(end, limit)))
        return adjusted
    return free_intervals

# List the candidate days in order.
days = ["Monday", "Tuesday", "Wednesday"]
scheduled_day = None
scheduled_start = None
scheduled_end = None

for day in days:
    # Calculate free intervals for Nicole.
    nicole_busy = [(time_to_minutes(s), time_to_minutes(e)) for s, e in schedules["Nicole"].get(day, [])]
    nicole_free = get_free_intervals(WORK_START, WORK_END, nicole_busy)

    # Calculate free intervals for Ruth.
    ruth_busy = [(time_to_minutes(s), time_to_minutes(e)) for s, e in schedules["Ruth"].get(day, [])]
    ruth_free = get_free_intervals(WORK_START, WORK_END, ruth_busy)
    
    # Apply Ruth's preference for Wednesday.
    if day == "Wednesday":
        ruth_free = apply_preference(ruth_free, day)
    
    # Find the common free intervals between Nicole and Ruth.
    common_free = intersect_intervals(nicole_free, ruth_free, MEETING_DURATION)
    
    # If a common free interval is found, schedule the meeting at the earliest possible time.
    if common_free:
        meeting_start = common_free[0][0]
        meeting_end = meeting_start + MEETING_DURATION
        scheduled_day = day
        scheduled_start = meeting_start
        scheduled_end = meeting_end
        break

if scheduled_day is not None:
    start_str = minutes_to_time(scheduled_start)
    end_str = minutes_to_time(scheduled_end)
    # Output in the required format: day and time range "HH:MM:HH:MM"
    print(f"{scheduled_day} {start_str}:{end_str}")
else:
    print("No available time slot found.")