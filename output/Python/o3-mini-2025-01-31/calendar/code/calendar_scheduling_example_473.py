def minutes(time_str):
    """Converts time in HH:MM format to minutes past midnight."""
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def time_str(minutes_val):
    """Converts minutes past midnight to HH:MM string format."""
    h = minutes_val // 60
    m = minutes_val % 60
    return f"{h:02d}:{m:02d}"

def subtract_intervals(working, busy):
    """Subtract busy intervals from a working interval.
       working: a tuple (start, end) in minutes.
       busy: a list of (start, end) busy times in minutes.
       Returns a list of free intervals (start, end).
    """
    free = []
    current_start = working[0]
    for bstart, bend in sorted(busy):
        if bstart > current_start:
            free.append((current_start, min(bstart, working[1])))
        current_start = max(current_start, bend)
    if current_start < working[1]:
        free.append((current_start, working[1]))
    return free

def intersect_intervals(int1, int2):
    """Intersects two lists of intervals.
       Each interval is a tuple (start,end).
       Returns the list of overlapping intervals.
    """
    res = []
    i, j = 0, 0
    while i < len(int1) and j < len(int2):
        start = max(int1[i][0], int2[j][0])
        end = min(int1[i][1], int2[j][1])
        if start < end:
            res.append((start, end))
        if int1[i][1] < int2[j][1]:
            i += 1
        else:
            j += 1
    return res

# Define working hours in minutes (Monday work hours: 09:00 to 17:00)
work_start = minutes("09:00")
work_end = minutes("17:00")
working_interval = (work_start, work_end)

# Busy times for each participant in minutes
schedules = {
    "Gregory": [("09:00", "09:30"), ("11:30", "12:00")],
    "Jonathan": [("09:00", "09:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
    "Barbara": [("10:00", "10:30"), ("13:30", "14:00")],
    "Jesse": [("10:00", "11:00"), ("12:30", "14:30")],
    "Alan": [("09:30", "11:00"), ("11:30", "12:30"), ("13:00", "15:30"), ("16:00", "17:00")],
    "Nicole": [("09:00", "10:30"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "17:00")],
    "Catherine": [("09:00", "10:30"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")]
}

# Convert schedule times to minutes
for person in schedules:
    schedules[person] = [(minutes(start), minutes(end)) for start, end in schedules[person]]

# Calculate free intervals for each participant within working hours
free_intervals = {}
for person, busy in schedules.items():
    free_intervals[person] = subtract_intervals(working_interval, busy)

# Intersect free intervals of all participants
# Start with the full working hours as the initial available intervals list
common_free = [working_interval]

for person in free_intervals:
    common_free = intersect_intervals(common_free, free_intervals[person])

# We need a meeting of duration 30 minutes.
meeting_duration = 30
proposed_slot = None

for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_slot = (start, start + meeting_duration)
        break

if proposed_slot:
    start_time = time_str(proposed_slot[0])
    end_time = time_str(proposed_slot[1])
    # Day of week is Monday as given in the task
    day = "Monday"
    print(f"{day} {start_time}:{end_time}")
else:
    print("No available slot found.")