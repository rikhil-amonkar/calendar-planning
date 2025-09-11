def main():
    # Define schedules for Nancy and Jose
    nancy_schedule = {
        'Monday': [(600, 630), (690, 750), (810, 840), (870, 930), (960, 1020)],
        'Tuesday': [(570, 630), (660, 690), (720, 750), (780, 810), (930, 960)],
        'Wednesday': [(600, 690), (810, 960)]
    }
    jose_schedule = {
        'Monday': [(540, 1020)],
        'Tuesday': [(540, 1020)],
        'Wednesday': [(540, 570), (600, 750), (810, 870), (900, 1020)]
    }

    days = ['Monday', 'Tuesday', 'Wednesday']
    for day in days:
        # Get busy intervals for the day
        nancy_buses = nancy_schedule.get(day, [])
        jose_buses = jose_schedule.get(day, [])

        # Compute free intervals for each
        nancy_free = get_free_intervals(nancy_buses)
        jose_free = get_free_intervals(jose_buses)

        # Find overlaps between free intervals
        overlaps = find_overlaps(nancy_free, jose_free)

        # Check for a 30-minute slot
        for start, end in overlaps:
            if end - start >= 30:
                # Convert to time strings
                start_time = minutes_to_time(start)
                end_time = minutes_to_time(start + 30)
                print(f"{day} {start_time}:{end_time}")
                return

def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    sorted_buses = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for start, end in sorted_buses:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_overlaps(list1, list2):
    i = 0
    j = 0
    overlaps = []
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlaps.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return overlaps

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

if __name__ == "__main__":
    main()