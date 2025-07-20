def format_minutes(m):
    h = m // 60
    minute = m % 60
    return f"{h:02d}:{minute:02d}"

def get_free_intervals(busy_intervals, start, end):
    if not busy_intervals:
        return [(start, end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = start
    for interval in sorted_busy:
        s, e = interval
        if current < s:
            free.append((current, s))
            current = e
        else:
            if e > current:
                current = e
    if current < end:
        free.append((current, end))
    return free

start_time = 720
end_time = 1020

daniel_busy = [(780, 810), (930, 960), (990, 1020)]
bradley_busy = [(720, 780), (810, 840), (930, 990)]

free_daniel = get_free_intervals(daniel_busy, start_time, end_time)
free_bradley = get_free_intervals(bradley_busy, start_time, end_time)

candidate = None
for d_int in free_daniel:
    for b_int in free_bradley:
        start_over = max(d_int[0], b_int[0])
        end_over = min(d_int[1], b_int[1])
        if end_over - start_over >= 30:
            candidate = (start_over, start_over + 30)
            break
    if candidate is not None:
        break

day_str = "Tuesday"
start_str = format_minutes(candidate[0])
end_str = format_minutes(candidate[1])
time_range_str = f"{start_str}:{end_str}"

print(day_str)
print(time_range_str)