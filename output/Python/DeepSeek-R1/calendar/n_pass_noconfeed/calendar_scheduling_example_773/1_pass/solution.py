def main():
    work_start = 540  # 9:00 in minutes from midnight
    work_end = 1020    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    busy_times = {
        'Monday': [
            [600, 690],   # 10:00 to 11:30
            [720, 780],   # 12:00 to 13:00
            [840, 870],   # 14:00 to 14:30
            [900, 1020]   # 15:00 to 17:00
        ],
        'Tuesday': [
            [630, 690],   # 10:30 to 11:30
            [720, 870],   # 12:00 to 14:30
            [900, 930],   # 15:00 to 15:30
            [960, 1020]   # 16:00 to 17:00
        ],
        'Wednesday': [
            [570, 690],   # 9:30 to 11:30
            [750, 840],   # 12:30 to 14:00
            [870, 930],   # 14:30 to 15:30
            [990, 1020]   # 16:30 to 17:00
        ]
    }

    for day in days:
        busy_list = busy_times[day]
        if not busy_list:
            free_interval = [work_start, work_end]
            if free_interval[1] - free_interval[0] >= 60:
                meeting_start = free_interval[0]
                meeting_end = meeting_start + 60
                start_hour = meeting_start // 60
                start_min = meeting_start % 60
                end_hour = meeting_end // 60
                end_min = meeting_end % 60
                time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                print(day)
                print(time_str)
                return
        
        sorted_busy = sorted(busy_list, key=lambda x: x[0])
        free_intervals = []
        current = work_start
        
        for interval in sorted_busy:
            if interval[0] > current:
                free_intervals.append([current, interval[0]])
            current = max(current, interval[1])
        if current < work_end:
            free_intervals.append([current, work_end])
        
        for free in free_intervals:
            start_free, end_free = free
            duration = end_free - start_free
            if duration >= 60:
                meeting_start = start_free
                meeting_end = meeting_start + 60
                start_hour = meeting_start // 60
                start_min = meeting_start % 60
                end_hour = meeting_end // 60
                end_min = meeting_end % 60
                time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                print(day)
                print(time_str)
                return

if __name__ == "__main__":
    main()