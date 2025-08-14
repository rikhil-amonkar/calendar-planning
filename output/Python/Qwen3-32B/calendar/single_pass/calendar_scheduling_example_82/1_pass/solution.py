# Define the meeting duration in minutes
meeting_duration = 30

# Work day in minutes (9:00 to 17:00 is 480 minutes)
start_day = 0
end_day = 8 * 60  # 480

# Participants' busy intervals
# Michael's busy intervals
michael_busy = [
    (30, 90),  # 9:30-10:30
    (360, 390),  # 15:00-15:30
    (420, 450)  # 16:00-16:30
]

# Arthur's busy intervals
arthur_busy = [
    (0, 180),  # 9:00-12:00
    (240, 360),  # 13:00-15:00
    (390, 420),  # 15:30-16:00
    (450, 480)  # 16:30-17:00
]

# Function to compute free intervals
def get_free_intervals(busy_intervals, start_day=0, end_day=480):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = start_day
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append( (prev_end, start) )
        prev_end = max(prev_end, end)
    if prev_end < end_day:
        free_intervals.append( (prev_end, end_day) )
    return free_intervals

# Get free intervals for each participant
michael_free = get_free_intervals(michael_busy)
arthur_free = get_free_intervals(arthur_busy)

# Function to find intersection of two lists of intervals
def interval_intersection(list_a, list_b):
    i = j = 0
    result = []
    while i < len(list_a) and j < len(list_b):
        a_start, a_end = list_a[i]
        b_start, b_end = list_b[j]
        # Calculate overlap
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append( (start, end) )
        # Move pointer
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

# Find common free intervals between Michael and Arthur
common_free = interval_intersection(michael_free, arthur_free)

# Now find the earliest interval in common_free that can fit the meeting
for interval in common_free:
    start, end = interval
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

# Convert to time format
def to_time(offset):
    total_hours = 9 + offset // 60
    total_mins = offset % 60
    return f"{total_hours:02d}:{total_mins:02d}"

start_time = to_time(meeting_start)
end_time = to_time(meeting_end)
day = "Monday"

print(f"{start_time}:{end_time} {day}")