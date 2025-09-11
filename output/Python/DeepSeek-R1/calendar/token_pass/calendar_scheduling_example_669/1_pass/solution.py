# Define work hours in minutes from midnight
work_start = 9 * 60  # 9:00
work_end = 17 * 60   # 17:00

# Meeting duration in minutes
meeting_duration = 30

# Define days to consider
days = ['Monday', 'Tuesday']

# Jean's busy intervals: list of (start_min, end_min) for each day
jean_busy = {
    'Monday': [],
    'Tuesday': [(11*60 + 30, 12*60), (16*60, 16*60 + 30)]  # 11:30-12:00 and 16:00-16:30
}

# Doris's busy intervals
doris_busy = {
    'Monday': [
        (9*60, 11*60 + 30),    # 9:00-11:30
        (12*60, 12*60 + 30),    # 12:00-12:30
        (13*60 + 30, 16*60),    # 13:30-16:00
        (16*60 + 30, 17*60)     # 16:30-17:00
    ],
    'Tuesday': [
        (9*60, 17*60)           # 9:00-17:00
    ]
}

# Doris's preference: avoid Monday after 14:00 (840 minutes from midnight)
preference_time = 14 * 60

# Function to find free intervals given busy intervals and work range
def find_free_intervals(busy_list, start, end):
    # Sort busy intervals by start time
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    free_list = []
    current = start
    for busy_start, busy_end in sorted_busy:
        if current < busy_start:
            free_list.append((current, busy_start))
        current = max(current, busy_end)
    if current < end:
        free_list.append((current, end))
    return free_list

# Function to find common free intervals between two sets of free intervals
def find_common_free(free1, free2):
    common = []
    i = j = 0
    while i < len(free1) and j < len(free2):
        start1, end1 = free1[i]
        start2, end2 = free2[j]
        start_max = max(start1, start2)
        end_min = min(end1, end2)
        if start_max < end_min:
            common.append((start_max, end_min))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return common

# Function to convert minutes to time string (e.g., 540 -> "9:00")
def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Iterate over days to find a suitable meeting time
found = False
for day in days:
    # Get free intervals for Jean and Doris on this day
    jean_free = find_free_intervals(jean_busy[day], work_start, work_end)
    doris_free = find_free_intervals(doris_busy[day], work_start, work_end)
    common_free = find_common_free(jean_free, doris_free)
    
    # Check common free intervals for sufficient duration
    for start, end in common_free:
        if end - start >= meeting_duration:
            # For Monday, check preference: avoid after 14:00
            if day == 'Monday':
                if end <= preference_time:  # interval ends by 14:00
                    meeting_start = start
                    meeting_end = meeting_start + meeting_duration
                    # Output the time and day
                    time_str = f"{min_to_time(meeting_start)}:{min_to_time(meeting_end)}"
                    print(f"{time_str} {day}")
                    found = True
                    break
            else:
                # For Tuesday or other days, use any suitable interval
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                time_str = f"{min_to_time(meeting_start)}:{min_to_time(meeting_end)}"
                print(f"{time_str} {day}")
                found = True
                break
    if found:
        break

# If no suitable time found (though problem says there is one), output a fallback
if not found:
    # Should not happen, but for safety
    print("No suitable time found")