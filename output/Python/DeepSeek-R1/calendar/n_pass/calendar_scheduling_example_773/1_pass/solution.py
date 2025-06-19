def main():
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    duration = 60        # 60 minutes (1 hour)

    # Busy intervals for Roy in minutes (start, end) for each day
    busy_intervals = {
        'Monday': [
            (10*60, 11*60 + 30),   # 10:00 to 11:30
            (12*60, 13*60),         # 12:00 to 13:00
            (14*60, 14*60 + 30),    # 14:00 to 14:30
            (15*60, 17*60)           # 15:00 to 17:00
        ],
        'Tuesday': [
            (10*60 + 30, 11*60 + 30), # 10:30 to 11:30
            (12*60, 14*60 + 30),      # 12:00 to 14:30
            (15*60, 15*60 + 30),      # 15:00 to 15:30
            (16*60, 17*60)            # 16:00 to 17:00
        ],
        'Wednesday': [
            (9*60 + 30, 11*60 + 30), # 9:30 to 11:30
            (12*60 + 30, 14*60),      # 12:30 to 14:00
            (14*60 + 30, 15*60 + 30), # 14:30 to 15:30
            (16*60 + 30, 17*60)       # 16:30 to 17:00
        ]
    }

    for day in days:
        free_intervals = [(work_start, work_end)]
        busy_today = busy_intervals[day]
        
        for busy_start, busy_end in busy_today:
            new_free = []
            for s, e in free_intervals:
                if busy_end <= s or busy_start >= e:
                    new_free.append((s, e))
                else:
                    if s < busy_start:
                        new_free.append((s, busy_start))
                    if busy_end < e:
                        new_free.append((busy_end, e))
            free_intervals = new_free
        
        free_intervals.sort(key=lambda x: x[0])
        
        for s, e in free_intervals:
            if e - s >= duration:
                meeting_start = s
                meeting_end = s + duration
                start_hour = meeting_start // 60
                start_minute = meeting_start % 60
                end_hour = meeting_end // 60
                end_minute = meeting_end % 60
                time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                print(day)
                print(time_str)
                return

if __name__ == "__main__":
    main()