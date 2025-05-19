def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    sorted_busy = sorted(busy, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_busy:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

# Define work hours (9:00-17:00) in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Tuesday schedules
patricia_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("12:00")),
    (time_to_minutes("14:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

jesse_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Calculate free intervals
patricia_free = get_free_intervals(patricia_busy, work_start, work_end)
jesse_free = get_free_intervals(jesse_busy, work_start, work_end)

# Find overlapping intervals
overlap = []
for p_start, p_end in patricia_free:
    for j_start, j_end in jesse_free:
        start = max(p_start, j_start)
        end = min(p_end, j_end)
        if start < end:
            overlap.append((start, end))

# Find the first interval with at least 60 minutes
for start, end in overlap:
    if end - start >= 60:
        day = "Tuesday"
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(start + 60)
        print(f"{day} {start_time}:{end_time}")
        exit()

# If no interval found (though problem states there is one)
print("No suitable time found")