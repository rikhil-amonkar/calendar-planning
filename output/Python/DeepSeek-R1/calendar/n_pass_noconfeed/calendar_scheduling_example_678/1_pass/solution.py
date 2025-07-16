def main():
    days = ['Monday', 'Tuesday']
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    meeting_duration = 60  # 60 minutes

    for day in days:
        busy_intervals = []
        if day == 'Monday':
            # Russell's Monday schedule: 10:30-11:00
            busy_intervals.append([10*60 + 30, 11*60])
            # Alexander's Monday schedule: 9:00-11:30, 12:00-14:30, 15:00-17:00
            busy_intervals.append([9*60, 11*60 + 30])
            busy_intervals.append([12*60, 14*60 + 30])
            busy_intervals.append([15*60, 17*60])
        elif day == 'Tuesday':
            # Russell's Tuesday schedule: 13:00-13:30
            busy_intervals.append([13*60, 13*60 + 30])
            # Alexander's Tuesday schedule: 9:00-10:00, 13:00-14:00, 15:00-15:30, 16:00-16:30
            busy_intervals.append([9*60, 10*60])
            busy_intervals.append([13*60, 14*60])
            busy_intervals.append([15*60, 15*60 + 30])
            busy_intervals.append([16*60, 16*60 + 30])
        
        # Merge overlapping busy intervals
        busy_intervals.sort(key=lambda x: x[0])
        merged_busy = []
        for interval in busy_intervals:
            if not merged_busy:
                merged_busy.append(interval)
            else:
                last_interval = merged_busy[-1]
                if interval[0] <= last_interval[1]:
                    last_interval[1] = max(last_interval[1], interval[1])
                else:
                    merged_busy.append(interval)
        
        # Compute free intervals within work hours
        free_intervals = []
        if not merged_busy:
            free_intervals.append([work_start, work_end])
        else:
            # Before first busy interval
            if merged_busy[0][0] > work_start:
                free_intervals.append([work_start, merged_busy[0][0]])
            
            # Between busy intervals
            for i in range(len(merged_busy) - 1):
                start_gap = merged_busy[i][1]
                end_gap = merged_busy[i+1][0]
                if start_gap < end_gap:
                    free_intervals.append([start_gap, end_gap])
            
            # After last busy interval
            if merged_busy[-1][1] < work_end:
                free_intervals.append([merged_busy[-1][1], work_end])
        
        # Check each free interval for a suitable meeting time
        for interval in free_intervals:
            s, e = interval
            if day == 'Tuesday':
                # Adjust start to at least 13:30 (810 minutes)
                adjusted_s = max(s, 13*60 + 30)
                if e - adjusted_s >= meeting_duration:
                    start_time = adjusted_s
                    end_time = adjusted_s + meeting_duration
                    # Format the time
                    start_hour = start_time // 60
                    start_minute = start_time % 60
                    end_hour = end_time // 60
                    end_minute = end_time % 60
                    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                    print(day)
                    print(time_str)
                    return
            else:
                if e - s >= meeting_duration:
                    start_time = s
                    end_time = s + meeting_duration
                    start_hour = start_time // 60
                    start_minute = start_time % 60
                    end_hour = end_time // 60
                    end_minute = end_time % 60
                    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                    print(day)
                    print(time_str)
                    return

if __name__ == "__main__":
    main()