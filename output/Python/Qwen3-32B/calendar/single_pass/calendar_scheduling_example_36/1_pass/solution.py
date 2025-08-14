def get_free_times(work_start, work_end, busy_intervals):
    free = []
    current_start = work_start
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    for start, end in sorted_busy:
        if start > current_start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def apply_denise_constraint(free_intervals):
    adjusted = []
    meeting_duration = 60
    max_end = 12 * 60 + 30  # 12:30 PM
    for start, end in free_intervals:
        new_end = min(end, max_end)
        if new_end - start >= meeting_duration:
            adjusted.append((start, new_end))
    return adjusted

def interval_intersection(a, b):
    i = 0
    j = 0
    res = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work day in minutes
work_start = 9 * 60
work_end = 17 * 60

# Participants' busy times
ryan_busy = [(9*60, 9*60 + 30), (12*60 + 30, 13*60)]  # 9:00-9:30, 12:30-13:00
denise_busy = [(9*60 + 30, 10*60 + 30), (12*60, 13*60), (14*60 + 30, 16*60 + 30)]  # 9:30-10:30, 12:00-13:00, 14:30-16:30

# Get free times for each
ryan_free = get_free_times(work_start, work_end, ryan_busy)
denise_free = get_free_times(work_start, work_end, denise_busy)

# Apply Denise's constraint
denise_adjusted = apply_denise_constraint(denise_free)

# Find intersection between ryan_free and denise_adjusted
overlapping = interval_intersection(ryan_free, denise_adjusted)

# Find earliest possible meeting time (1 hour)
if overlapping:
    earliest = overlapping[0]
    meeting_start = earliest[0]
    meeting_end = meeting_start + 60
    start_str = to_time_str(meeting_start)
    end_str = to_time_str(meeting_end)
    day = "Monday"
    print(f"{start_str}:{end_str} {day}")
else:
    print("No available time")