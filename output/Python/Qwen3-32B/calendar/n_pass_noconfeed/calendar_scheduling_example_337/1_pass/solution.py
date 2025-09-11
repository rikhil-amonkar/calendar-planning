def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, start_work, end_work):
    busy_intervals.sort()
    free = []
    current_start = start_work
    for start, end in busy_intervals:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < end_work:
        free.append((current_start, end_work))
    return free

def intersect_intervals(intervals1, intervals2):
    i = 0
    j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

participants = {
    'John': [(11*60 + 30, 12*60), (14*60, 14*60 + 30)],
    'Megan': [(12*60, 12*60 + 30), (14*60, 15*60), (15*60 + 30, 16*60)],
    'Brandon': [],
    'Kimberly': [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 14*60 + 30), (15*60, 16*60), (16*60 + 30, 17*60)],
    'Sean': [(10*60, 11*60), (11*60 + 30, 14*60), (15*60, 15*60 + 30)],
    'Lori': [(9*60, 9*60 + 30), (10*60 + 30, 12*60), (13*60, 14*60 + 30), (16*60, 16*60 + 30)]
}

start_work = 9 * 60  # 540 minutes
end_work = 17 * 60   # 1020 minutes

# Compute free intervals for each participant
free_intervals_list = []
for name in participants:
    busy = participants[name]
    free = get_free_intervals(busy, start_work, end_work)
    free_intervals_list.append(free)

# Compute the intersection of all free intervals
global_free = free_intervals_list[0]
for i in range(1, len(free_intervals_list)):
    global_free = intersect_intervals(global_free, free_intervals_list[i])

# Find the earliest suitable meeting time
meeting_start = None
meeting_end = None
for interval in global_free:
    start, end = interval
    if end - start >= 30:
        meeting_start = start
        meeting_end = start + 30
        break

time_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
day = "Monday"
print(f"{time_range} {day}")