def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    meeting_duration = 60  # 60 minutes

    # Busy intervals for Bryan and Nicholas for each day (in minutes since start of day)
    busy_intervals = {
        'Bryan': {
            'Monday': [],
            'Tuesday': [],
            'Wednesday': [],
            'Thursday': [(9*60+30, 10*60), (12*60+30, 13*60)],  # 9:30-10:00, 12:30-13:00
            'Friday': [(10*60+30, 11*60), (14*60, 14*60+30)]     # 10:30-11:00, 14:00-14:30
        },
        'Nicholas': {
            'Monday': [(11*60+30, 12*60), (13*60, 15*60+30)],   # 11:30-12:00, 13:00-15:30
            'Tuesday': [(9*60, 9*60+30), (11*60, 13*60+30), (14*60, 16*60+30)], # 9:00-9:30, 11:00-13:30, 14:00-16:30
            'Wednesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 13*60+30), (14*60, 14*60+30), (15*60, 16*60+30)], # 9:00-9:30, 10:00-11:00, 11:30-13:30, 14:00-14:30, 15:00-16:30
            'Thursday': [(10*60+30, 11*60+30), (12*60, 12*60+30), (15*60, 15*60+30), (16*60+30, 17*60)], # 10:30-11:30, 12:00-12:30, 15:00-15:30, 16:30-17:00
            'Friday': [(9*60, 10*60+30), (11*60, 12*60), (12*60+30, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)] # 9:00-10:30, 11:00-12:00, 12:30-14:30, 15:30-16:00, 16:30-17:00
        }
    }

    # Days to check in priority order (avoid Tuesday for Bryan, avoid Monday/Thursday for Nicholas)
    days = ['Wednesday', 'Friday', 'Tuesday', 'Monday', 'Thursday']

    # Function to compute free intervals given busy intervals
    def get_free_intervals(busy_list, start_bound, end_bound):
        if not busy_list:
            return [(start_bound, end_bound)]
        sorted_busy = sorted(busy_list, key=lambda x: x[0])
        free = []
        current = start_bound
        for s, e in sorted_busy:
            if current < s:
                free.append((current, s))
            current = max(current, e)
        if current < end_bound:
            free.append((current, end_bound))
        return free

    # Function to find intersection of two sets of intervals
    def intersect_intervals(intervals_a, intervals_b):
        i, j = 0, 0
        intersection = []
        while i < len(intervals_a) and j < len(intervals_b):
            low = max(intervals_a[i][0], intervals_b[j][0])
            high = min(intervals_a[i][1], intervals_b[j][1])
            if low < high:
                intersection.append((low, high))
            if intervals_a[i][1] < intervals_b[j][1]:
                i += 1
            else:
                j += 1
        return intersection

    # Convert minutes to HH:MM string
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Iterate through days in priority order
    for day in days:
        bryan_busy = busy_intervals['Bryan'][day]
        nicholas_busy = busy_intervals['Nicholas'][day]
        
        bryan_free = get_free_intervals(bryan_busy, work_start, work_end)
        nicholas_free = get_free_intervals(nicholas_busy, work_start, work_end)
        
        common_free = intersect_intervals(bryan_free, nicholas_free)
        
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                time_range_str = f"{start_str}:{end_str}"
                # Output day and time range
                print(day)
                print(time_range_str)
                return

    # Fallback: if no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()