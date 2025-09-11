def main():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    duration = 30         # meeting duration in minutes

    # Daniel's busy times in minutes for each day
    daniel_busy = {
        'Monday': [(570, 630), (720, 750), (780, 840), (870, 900), (930, 960)],
        'Tuesday': [(660, 720), (780, 810), (930, 960), (990, 1020)],
        'Wednesday': [(540, 600), (840, 870)],
        'Thursday': [(630, 660), (720, 780), (870, 900), (930, 960)],
        'Friday': [(540, 570), (690, 720), (780, 810), (990, 1020)]
    }

    # Bradley's busy times in minutes for each day
    bradley_busy = {
        'Monday': [(570, 660), (690, 720), (750, 780), (840, 900)],
        'Tuesday': [(630, 660), (720, 780), (810, 840), (930, 990)],
        'Wednesday': [(540, 600), (660, 780), (810, 840), (870, 1020)],
        'Thursday': [(540, 750), (810, 840), (870, 900), (930, 990)],
        'Friday': [(540, 570), (600, 750), (780, 810), (840, 870), (930, 990)]
    }

    # Function to get free intervals from busy list
    def get_free_intervals(busy_list, start, end):
        busy_list.sort(key=lambda x: x[0])
        free_intervals = []
        current = start
        for busy in busy_list:
            if current < busy[0]:
                free_intervals.append((current, busy[0]))
            current = max(current, busy[1])
        if current < end:
            free_intervals.append((current, end))
        return free_intervals

    # Function to find common free intervals between two sets
    def intersect_intervals(intervals1, intervals2):
        common = []
        i = j = 0
        while i < len(intervals1) and j < len(intervals2):
            a, b = intervals1[i]
            c, d = intervals2[j]
            start_max = max(a, c)
            end_min = min(b, d)
            if start_max < end_min:
                common.append((start_max, end_min))
            if b < d:
                i += 1
            else:
                j += 1
        return common

    # Function to convert minutes to HH:MM string
    def min_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Check days in preferred order: Tuesday first (after 12:00), then others
    days = ['Tuesday', 'Wednesday', 'Thursday', 'Monday', 'Friday']
    for day in days:
        d_free = get_free_intervals(daniel_busy[day], work_start, work_end)
        b_free = get_free_intervals(bradley_busy[day], work_start, work_end)
        common_free = intersect_intervals(d_free, b_free)
        
        # For Tuesday, only consider times after 12:00 (720 minutes)
        if day == 'Tuesday':
            adjusted_free = []
            for start, end in common_free:
                if end > 720:
                    start_adj = max(start, 720)
                    if start_adj < end:
                        adjusted_free.append((start_adj, end))
            common_free = adjusted_free
        
        # For other days, no time adjustment for preferences in this case
        # Find a slot of duration in common free intervals
        for start, end in common_free:
            if end - start >= duration:
                start_time = start
                end_time = start_time + duration
                # Output the time and day
                time_str = f"{min_to_time(start_time)}:{min_to_time(end_time)}"
                print(f"{time_str}")
                print(day)
                return

    # If no time found, but problem states there is a solution
    print("No time found, but there should be a solution.")

if __name__ == "__main__":
    main()