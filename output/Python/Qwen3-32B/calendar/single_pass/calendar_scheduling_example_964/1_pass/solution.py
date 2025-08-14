def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_slot(merged):
    work_start = 540  # 9:00 AM
    work_end = 1020   # 5:00 PM

    if not merged:
        return (work_start, work_start + 60)

    first_start = merged[0][0]
    if first_start > work_start:
        free_start = work_start
        free_end = first_start
        if free_end - free_start >= 60:
            return (free_start, free_start + 60)

    for i in range(1, len(merged)):
        prev_end = merged[i-1][1]
        curr_start = merged[i][0]
        if curr_start > prev_end:
            free_start = prev_end
            free_end = curr_start
            if free_end - free_start >= 60:
                return (free_start, free_start + 60)

    last_end = merged[-1][1]
    if last_end < work_end:
        free_start = last_end
        free_end = work_end
        if free_end - free_start >= 60:
            return (free_start, free_start + 60)

    return None

def main():
    betty_schedule = {
        'Monday': [(600, 630), (690, 750), (960, 990)],
        'Tuesday': [(570, 600), (630, 660), (720, 750), (810, 900), (990, 1020)],
        'Wednesday': [(810, 840), (870, 900)],
        'Friday': [(540, 600), (690, 720), (750, 780), (870, 900)],
    }

    megan_schedule = {
        'Monday': [(540, 1020)],
        'Tuesday': [(540, 570), (600, 630), (720, 840), (900, 930), (960, 990)],
        'Wednesday': [(570, 630), (660, 690), (750, 780), (810, 870), (930, 1020)],
        'Thursday': [(540, 630), (690, 840), (870, 900), (930, 990)],
        'Friday': [(540, 1020)],
    }

    allowed_days = ['Monday', 'Tuesday', 'Friday']

    for day in allowed_days:
        betty_buses = betty_schedule.get(day, [])
        megan_buses = megan_schedule.get(day, [])
        all_buses = betty_buses + megan_buses

        merged = merge_intervals(all_buses)
        free_slot = find_free_slot(merged)
        if free_slot:
            start_time = minutes_to_time(free_slot[0])
            end_time = minutes_to_time(free_slot[1])
            print(f"{day} {start_time}:{end_time}")
            return

if __name__ == "__main__":
    main()