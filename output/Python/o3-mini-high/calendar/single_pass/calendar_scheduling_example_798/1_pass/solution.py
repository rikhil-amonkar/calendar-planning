def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    free_intervals = []
    current = work_start
    # Sort busy intervals by their start time
    for start_str, end_str in sorted(busy_intervals, key=lambda x: time_to_minutes(x[0])):
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2, duration):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        inter_start = max(start1, start2)
        inter_end = min(end1, end2)
        if inter_end - inter_start >= duration:
            intersections.append((inter_start, inter_end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_common_slot(list_of_free_intervals, duration):
    # Start with the free intervals of the first participant.
    common = list_of_free_intervals[0]
    for free in list_of_free_intervals[1:]:
        common = intersect_intervals(common, free, duration)
        if not common:
            break
    return common

# Meeting details
MEETING_DURATION = 30  # in minutes
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")

# Schedules for each day for Nancy and Jose.
schedules = {
    "Monday": {
        "Nancy": [("10:00", "10:30"), ("11:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Jose": [("09:00", "17:00")]
    },
    "Tuesday": {
        "Nancy": [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00")],
        "Jose": [("09:00", "17:00")]
    },
    "Wednesday": {
        "Nancy": [("10:00", "11:30"), ("13:30", "16:00")],
        "Jose": [("09:00", "9:30"), ("10:00", "12:30"), ("13:30", "14:30"), ("15:00", "17:00")]
    }
}

selected_day = None
selected_slot = None

# Check days in the preferred order: Monday, Tuesday, then Wednesday.
for day in ["Monday", "Tuesday", "Wednesday"]:
    participants = schedules[day]
    free_intervals_list = []
    for person in participants:
        busy = participants[person]
        free_intervals = compute_free_intervals(busy, WORK_START, WORK_END)
        free_intervals_list.append(free_intervals)
    common_slots = find_common_slot(free_intervals_list, MEETING_DURATION)
    if common_slots:
        # Choose the earliest slot that can fit the meeting.
        for start, end in common_slots:
            if end - start >= MEETING_DURATION:
                selected_day = day
                selected_slot = (start, start + MEETING_DURATION)
                break
    if selected_day:
        break

if selected_day and selected_slot:
    start_time = minutes_to_time(selected_slot[0])
    end_time = minutes_to_time(selected_slot[1])
    print(f"{selected_day} {start_time}:{end_time}")
else:
    print("No available meeting slot found.")