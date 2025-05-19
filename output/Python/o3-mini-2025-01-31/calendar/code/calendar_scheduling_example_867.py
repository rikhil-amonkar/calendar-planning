def time_to_minutes(t):
    # Convert "HH:MM" to total minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight to "HH:MM" string.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Define working hours (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Busy schedules for each participant.
# Each busy interval is given as [start, end] in "HH:MM" format.
schedules = {
    "Betty": {
        "Monday": [["10:00", "10:30"],
                   ["13:30", "14:00"],
                   ["15:00", "15:30"],
                   ["16:00", "16:30"]],
        "Tuesday": [["09:00", "09:30"],
                    ["11:30", "12:00"],
                    ["12:30", "13:00"],
                    ["13:30", "14:00"],
                    ["16:30", "17:00"]],
        "Wednesday": [["09:30", "10:30"],
                      ["13:00", "13:30"],
                      ["14:00", "14:30"]],
        "Thursday": [["09:30", "10:00"],
                     ["11:30", "12:00"],
                     ["14:00", "14:30"],
                     ["15:00", "15:30"],
                     ["16:30", "17:00"]]
    },
    "Scott": {
        "Monday": [["09:30", "15:00"],
                   ["15:30", "16:00"],
                   ["16:30", "17:00"]],
        "Tuesday": [["09:00", "09:30"],
                    ["10:00", "11:00"],
                    ["11:30", "12:00"],
                    ["12:30", "13:30"],
                    ["14:00", "15:00"],
                    ["16:00", "16:30"]],
        "Wednesday": [["09:30", "12:30"],
                      ["13:00", "13:30"],
                      ["14:00", "14:30"],
                      ["15:00", "15:30"],
                      ["16:00", "16:30"]],
        "Thursday": [["09:00", "09:30"],
                     ["10:00", "10:30"],
                     ["11:00", "12:00"],
                     ["12:30", "13:00"],
                     ["15:00", "16:00"],
                     ["16:30", "17:00"]]
    }
}

# Additional constraints:
# 1. Betty cannot meet on Monday.
# 2. On Tuesday and Thursday, Betty cannot meet before 15:00.
# 3. Scott would like to avoid Wednesday if possible.
# Priority: try Tuesday and Thursday first, then Wednesday if needed.
candidate_days = ["Tuesday", "Thursday", "Wednesday"]

def get_free_intervals(busy_intervals):
    """Compute free intervals within working hours given busy intervals.
       busy_intervals: list of [start, end] in minutes.
    """
    free = []
    current = work_start
    # Sort the busy intervals by start time.
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    for interval in busy_intervals:
        start, end = interval
        if start > current:
            free.append([current, start])
        current = max(current, end)
    if current < work_end:
        free.append([current, work_end])
    return free

def intervals_intersection(intervals1, intervals2):
    """Find intersection of two list of intervals."""
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start + meeting_duration <= end:
            result.append([start, end])
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

def convert_busy_list(busy_list):
    """Convert list of busy intervals from string to minutes."""
    return [[time_to_minutes(start), time_to_minutes(end)] for start, end in busy_list]

# Try each candidate day
for day in candidate_days:
    # Skip Monday because Betty cannot meet on Monday.
    if day == "Monday":
        continue

    # Get busy intervals for Betty and Scott
    betty_busy = convert_busy_list(schedules["Betty"].get(day, []))
    scott_busy = convert_busy_list(schedules["Scott"].get(day, []))

    # Compute free intervals within working hours.
    betty_free = get_free_intervals(betty_busy)
    scott_free = get_free_intervals(scott_busy)

    # On Tuesday and Thursday, add constraint: meeting can start only at or after 15:00.
    constraint_start = work_start
    if day in ["Tuesday", "Thursday"]:
        constraint_start = max(work_start, time_to_minutes("15:00"))
    # Adjust free intervals for Betty to account for her constraint if needed.
    betty_free_adjusted = []
    for interval in betty_free:
        # If the interval ends before the constraint, skip it.
        if interval[1] <= constraint_start:
            continue
        # Adjust start if needed.
        start = max(interval[0], constraint_start)
        betty_free_adjusted.append([start, interval[1]])

    # Similarly adjust Scott's free intervals (though only Betty has explicit constraint).
    scott_free_adjusted = []
    for interval in scott_free:
        if interval[1] <= constraint_start:
            continue
        start = max(interval[0], constraint_start)
        scott_free_adjusted.append([start, interval[1]])

    # Find common free intervals between Betty and Scott.
    common_free = intervals_intersection(betty_free_adjusted, scott_free_adjusted)

    # Check if any free interval has enough duration for the meeting.
    for interval in common_free:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            # Output in the required format.
            time_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
            print(f"{day} {time_range}")
            exit(0)

# If no slot found (but the problem guarantees a solution)
print("No available slot")