def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes

    # Define busy intervals for Gary and David for Monday and Tuesday
    busy = {
        'Gary': {
            'Monday': [(570, 600), (660, 780), (840, 870), (990, 1020)],
            'Tuesday': [(540, 570), (630, 660), (870, 960)]
        },
        'David': {
            'Monday': [(540, 570), (600, 780), (870, 990)],
            'Tuesday': [(540, 570), (600, 630), (660, 750), (780, 870), (900, 960), (990, 1020)]
        }
    }

    # Function to compute free intervals given work hours and busy intervals
    def compute_free(work_start, work_end, busy_intervals):
        if not busy_intervals:
            return [(work_start, work_end)]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = work_start
        for s, e in sorted_busy:
            if current < s:
                free.append((current, s))
            current = max(current, e)
        if current < work_end:
            free.append((current, work_end))
        return free

    # Function to find intersection of two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        i, j = 0, 0
        common = []
        while i < len(intervals1) and j < len(intervals2):
            low = max(intervals1[i][0], intervals2[j][0])
            high = min(intervals1[i][1], intervals2[j][1])
            if low < high:
                common.append((low, high))
            if intervals1[i][1] < intervals2[j][1]:
                i += 1
            else:
                j += 1
        return common

    # Check each day for a common free slot of at least 60 minutes
    days = ['Monday', 'Tuesday']
    for day in days:
        free_gary = compute_free(work_start, work_end, busy['Gary'][day])
        free_david = compute_free(work_start, work_end, busy['David'][day])
        common_free = intersect_intervals(free_gary, free_david)
        
        for s, e in common_free:
            if e - s >= 60:
                meeting_end = s + 60
                start_hour, start_min = divmod(s, 60)
                end_hour, end_min = divmod(meeting_end, 60)
                time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                print(day)
                print(time_str)
                return
                
    # If no slot found, but problem states there is a solution
    print("No suitable time found, but a solution exists.")

if __name__ == "__main__":
    main()