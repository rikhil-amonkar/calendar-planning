def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # minutes

    # Busy intervals in minutes (half-open [start, end))
    busy = {
        'Olivia': [
            [12*60+30, 13*60+30],  # 12:30-13:30
            [14*60+30, 15*60+0],    # 14:30-15:00
            [16*60+30, 17*60+0]     # 16:30-17:00
        ],
        'Anna': [],  # No meetings
        'Virginia': [
            [9*60+0, 10*60+0],     # 9:00-10:00
            [11*60+30, 16*60+0],    # 11:30-16:00
            [16*60+30, 17*60+0]     # 16:30-17:00
        ],
        'Paul': [
            [9*60+0, 9*60+30],      # 9:00-9:30
            [11*60+0, 11*60+30],    # 11:00-11:30
            [13*60+0, 14*60+0],     # 13:00-14:00
            [14*60+30, 16*60+0],    # 14:30-16:00
            [16*60+30, 17*60+0]     # 16:30-17:00
        ]
    }

    # Function to compute free intervals
    def get_free_intervals(busy_intervals, start_bound, end_bound):
        if not busy_intervals:
            return [[start_bound, end_bound]]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = start_bound
        for s, e in sorted_busy:
            if current < s:
                free.append([current, s])
            current = max(current, e)
        if current < end_bound:
            free.append([current, end_bound])
        return free

    # Function to intersect two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        if not intervals1 or not intervals2:
            return []
        i, j = 0, 0
        result = []
        while i < len(intervals1) and j < len(intervals2):
            a_start, a_end = intervals1[i]
            b_start, b_end = intervals2[j]
            start = max(a_start, b_start)
            end = min(a_end, b_end)
            if start < end:
                result.append([start, end])
            if a_end < b_end:
                i += 1
            else:
                j += 1
        return result

    # Get free intervals for each participant
    participants = ['Olivia', 'Anna', 'Virginia', 'Paul']
    free_intervals_all = []
    for p in participants:
        free = get_free_intervals(busy[p], work_start, work_end)
        free_intervals_all.append(free)

    # Compute common free intervals
    common_free = free_intervals_all[0]
    for i in range(1, len(participants)):
        common_free = intersect_intervals(common_free, free_intervals_all[i])
        if not common_free:
            break

    # Find first suitable meeting time
    meeting_start = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break

    # Convert minutes to HH:MM format
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    if meeting_start is None:
        print("No suitable time found")
    else:
        start_str = format_time(meeting_start)
        end_str = format_time(meeting_end)
        print("Monday")
        print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()