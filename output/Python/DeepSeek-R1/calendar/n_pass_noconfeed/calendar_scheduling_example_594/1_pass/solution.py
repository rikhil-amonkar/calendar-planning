def main():
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes (half-open: [0, 480))
    work_start = 0
    work_end = 480
    meeting_duration = 30

    # Busy intervals for Adam and Roy in minutes (half-open: [start, end))
    adam_busy = [
        (30, 60),    # 9:30-10:00
        (210, 240),  # 12:30-13:00
        (330, 360),  # 14:30-15:00
        (450, 480)   # 16:30-17:00
    ]
    
    roy_busy = [
        (60, 120),   # 10:00-11:00
        (150, 240),  # 11:30-13:00
        (270, 330),  # 13:30-14:30
        (450, 480)   # 16:30-17:00
    ]
    
    # Function to compute free intervals given busy intervals and work hours
    def get_free_intervals(busy_list, start, end):
        free = [(start, end)]
        for busy in busy_list:
            new_free = []
            for interval in free:
                if interval[1] <= busy[0] or interval[0] >= busy[1]:
                    new_free.append(interval)
                else:
                    if interval[0] < busy[0]:
                        new_free.append((interval[0], busy[0]))
                    if interval[1] > busy[1]:
                        new_free.append((busy[1], interval[1]))
            free = new_free
        return free
    
    # Get free intervals for Adam and Roy
    free_adam = get_free_intervals(adam_busy, work_start, work_end)
    free_roy = get_free_intervals(roy_busy, work_start, work_end)
    
    # Find intersection of free intervals
    def intersect_intervals(list1, list2):
        i = j = 0
        result = []
        while i < len(list1) and j < len(list2):
            a = list1[i]
            b = list2[j]
            start = max(a[0], b[0])
            end = min(a[1], b[1])
            if start < end:
                result.append((start, end))
            if a[1] < b[1]:
                i += 1
            else:
                j += 1
        return result
    
    free_both = intersect_intervals(free_adam, free_roy)
    
    # Find the earliest interval that can fit the meeting
    meeting_start = None
    for interval in free_both:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    # Convert meeting start and end to time strings
    def minutes_to_time(total_minutes):
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    if meeting_start is not None:
        meeting_end = meeting_start + meeting_duration
        start_time_str = minutes_to_time(meeting_start)
        end_time_str = minutes_to_time(meeting_end)
        time_range_str = f"{start_time_str}:{end_time_str}"
        print("Monday")
        print(time_range_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()