def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def intersect_intervals(a, b):
    i = 0
    j = 0
    result = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        # Move the pointer
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Work hours in minutes
work_start = 9 * 60
work_end = 17 * 60

# Participants' busy intervals
denise_busy = [(12 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]
natalie_busy = [(9 * 60, 11 * 60 + 30), (12 * 60, 13 * 60), (14 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)]
angela_busy = []

# Generate free intervals
denise_free = get_free_intervals(denise_busy, work_start, work_end)
natalie_free = get_free_intervals(natalie_busy, work_start, work_end)
angela_free = get_free_intervals(angela_busy, work_start, work_end)

# Compute group free intervals
group_free = intersect_intervals(denise_free, natalie_free)
group_free = intersect_intervals(group_free, angela_free)

# Find earliest meeting time of 30 minutes
meeting_duration = 30
for interval in group_free:
    start, end = interval
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = meeting_start + meeting_duration
        break

# Format output
start_time = min_to_time(meeting_start)
end_time = min_to_time(meeting_end)
print(f"{start_time}:{end_time} Monday")