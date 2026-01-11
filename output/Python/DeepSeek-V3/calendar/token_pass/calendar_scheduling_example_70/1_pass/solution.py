def time_to_minutes(t):
    """Convert HH:MM to minutes from midnight"""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from midnight to HH:MM"""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def busy_to_free(busy_intervals, work_start, work_end):
    """Convert busy intervals to free intervals within work hours"""
    free = []
    prev_end = work_start
    for start, end in sorted(busy_intervals):
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def intersect_free(free1, free2):
    """Intersect two lists of free intervals"""
    i, j = 0, 0
    result = []
    while i < len(free1) and j < len(free2):
        start = max(free1[i][0], free2[j][0])
        end = min(free1[i][1], free2[j][1])
        if start < end:
            result.append((start, end))
        if free1[i][1] < free2[j][1]:
            i += 1
        else:
            j += 1
    return result

def find_earliest_slot(free_intervals, duration):
    """Find earliest slot of given duration in free intervals"""
    for start, end in free_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    # Work hours 9:00 to 17:00
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes

    # Busy intervals in minutes from midnight
    denise_busy = [
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ]
    angela_busy = []
    natalie_busy = [
        (time_to_minutes("9:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ]

    # Convert to free intervals within work hours
    denise_free = busy_to_free(denise_busy, work_start, work_end)
    angela_free = busy_to_free(angela_busy, work_start, work_end)
    natalie_free = busy_to_free(natalie_busy, work_start, work_end)

    # Intersect all
    free_intersect = intersect_free(denise_free, angela_free)
    free_intersect = intersect_free(free_intersect, natalie_free)

    # Find earliest slot
    slot = find_earliest_slot(free_intersect, duration)
    if slot:
        start_m, end_m = slot
        start_time = minutes_to_time(start_m)
        end_time = minutes_to_time(end_m)
        print(f"{start_time}:{end_time}")
        print("Monday")
    else:
        print("No slot found")

if __name__ == "__main__":
    main()