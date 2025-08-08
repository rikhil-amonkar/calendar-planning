def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to an HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    # Sort intervals by start time.
    intervals.sort(key=lambda x: x[0])
    merged = [list(intervals[0])]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            last[1] = max(last[1], current[1])
        else:
            merged.append(list(current))
    return merged

def get_common_free_intervals(day, schedules, work_start, work_end):
    """Return common free intervals during work hours for all participants on a given day."""
    # Collect busy intervals from every participant for the day.
    busy_intervals = []
    for person in schedules:
        busy_intervals.extend(schedules[person].get(day, []))
    
    # Merge overlapping busy intervals.
    merged_busy = merge_intervals(busy_intervals)
    
    free_intervals = []
    current_start = work_start
    for interval in merged_busy:
        busy_start, busy_end = interval
        if busy_start > current_start:
            free_intervals.append((current_start, busy_start))
        current_start = max(current_start, busy_end)
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    
    return free_intervals

# Meeting duration (in minutes)
meeting_duration = 30

# Define work hours (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Define each participant's busy schedule in minutes (start, end)
# Times are represented as minutes past midnight.
schedules = {
    "Joshua": {
        "Monday": [(time_to_minutes("15:00"), time_to_minutes("15:30"))],
        "Tuesday": [(time_to_minutes("11:30"), time_to_minutes("12:00")),
                    (time_to_minutes("13:00"), time_to_minutes("13:30")),
                    (time_to_minutes("14:30"), time_to_minutes("15:00"))],
        "Wednesday": []  # Joshua is free all day on Wednesday
    },
    "Joyce": {
        "Monday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                   (time_to_minutes("10:00"), time_to_minutes("11:00")),
                   (time_to_minutes("11:30"), time_to_minutes("12:30")),
                   (time_to_minutes("13:00"), time_to_minutes("15:00")),
                   (time_to_minutes("15:30"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("17:00"))],  # Busy all day Tuesday
        "Wednesday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                      (time_to_minutes("10:00"), time_to_minutes("11:00")),
                      (time_to_minutes("12:30"), time_to_minutes("15:30")),
                      (time_to_minutes("16:00"), time_to_minutes("16:30"))]
    }
}

# Additional constraint: Joyce would prefer not to meet on Monday before 12:00.
def apply_preferences(day, start):
    if day == "Monday":
        preferred_start = time_to_minutes("12:00")
        return max(start, preferred_start)
    return start

# Days allowed for meeting.
days = ["Monday", "Tuesday", "Wednesday"]

meeting_found = False
for day in days:
    free_intervals = get_common_free_intervals(day, schedules, work_start, work_end)
    for interval_start, interval_end in free_intervals:
        # On Monday, adjust the start time if it is before 12:00 per Joyce's preference.
        candidate_start = apply_preferences(day, interval_start)
        if interval_end - candidate_start >= meeting_duration:
            meeting_start = candidate_start
            meeting_end = meeting_start + meeting_duration
            meeting_found = True
            break
    if meeting_found:
        chosen_day = day
        break

if meeting_found:
    # Format the output as "HH:MM:HH:MM Day"
    output = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} {chosen_day}"
    print(output)
else:
    print("No common time found for a 30-minute meeting.")