def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    free = []
    current = work_start
    # Ensure the busy intervals are sorted
    for b_start, b_end in sorted(busy_intervals):
        if current < b_start:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_interval_lists(list1, list2):
    intersections = []
    for start1, end1 in list1:
        for start2, end2 in list2:
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                intersections.append((start, end))
    return intersections

def find_meeting_slot(intervals, duration):
    # Sort the intervals by start time
    intervals = sorted(intervals, key=lambda x: x[0])
    for start, end in intervals:
        if end - start >= duration:
            return (start, start + duration)
    return None

# Define working hours: 9:00 to 17:00 (in minutes)
work_start = 9 * 60     # 540
work_end = 17 * 60      # 1020
meeting_duration = 30   # 30 minutes

# Anna's preference: not before 14:30 (870 minutes)
anna_pref_start = 14 * 60 + 30  # 870

# Busy intervals for each participant (times in minutes)
# Adam: 14:00-15:00
adam_busy = [(14 * 60, 15 * 60)]

# John: 13:00-13:30, 14:00-14:30, 15:30-16:00, 16:30-17:00
john_busy = [
    (13 * 60, 13 * 60 + 30),
    (14 * 60, 14 * 60 + 30),
    (15 * 60 + 30, 16 * 60),
    (16 * 60 + 30, 17 * 60)
]

# Stephanie: 9:30-10:00, 10:30-11:00, 11:30-16:00, 16:30-17:00
stephanie_busy = [
    (9 * 60 + 30, 10 * 60),
    (10 * 60 + 30, 11 * 60),
    (11 * 60 + 30, 16 * 60),
    (16 * 60 + 30, 17 * 60)
]

# Anna: 9:30-10:00, 12:00-12:30, 13:00-15:30, 16:30-17:00
anna_busy = [
    (9 * 60 + 30, 10 * 60),
    (12 * 60, 12 * 60 + 30),
    (13 * 60, 15 * 60 + 30),
    (16 * 60 + 30, 17 * 60)
]

# Calculate free intervals during working hours for each person
adam_free = get_free_intervals(adam_busy, work_start, work_end)
john_free = get_free_intervals(john_busy, work_start, work_end)
stephanie_free = get_free_intervals(stephanie_busy, work_start, work_end)
anna_free = get_free_intervals(anna_busy, work_start, work_end)

# Adjust free intervals with Anna's preference (not before 14:30)
preference_interval = [(anna_pref_start, work_end)]
adam_free = intersect_interval_lists(adam_free, preference_interval)
john_free = intersect_interval_lists(john_free, preference_interval)
stephanie_free = intersect_interval_lists(stephanie_free, preference_interval)
anna_free = intersect_interval_lists(anna_free, preference_interval)

# Find the intersection of free intervals for all participants
common_free = intersect_interval_lists(adam_free, john_free)
common_free = intersect_interval_lists(common_free, stephanie_free)
common_free = intersect_interval_lists(common_free, anna_free)

# Choose a meeting slot that fits the duration (30 minutes)
meeting_slot = find_meeting_slot(common_free, meeting_duration)

if meeting_slot:
    start, end = meeting_slot
    start_str = minutes_to_str(start)
    end_str = minutes_to_str(end)
    day = "Monday"
    # Output in the format HH:MM:HH:MM along with the day
    print(f"{day} {start_str}:{end_str}")
else:
    print("No available meeting slot found.")