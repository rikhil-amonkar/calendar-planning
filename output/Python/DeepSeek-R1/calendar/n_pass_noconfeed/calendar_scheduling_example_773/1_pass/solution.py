def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    meeting_duration = 60  # minutes

    # Roy's busy times for each day (as list of start-end string tuples)
    roy_busy = {
        'Monday': [('10:00', '11:30'), ('12:00', '13:00'), ('14:00', '14:30'), ('15:00', '17:00')],
        'Tuesday': [('10:30', '11:30'), ('12:00', '14:30'), ('15:00', '15:30'), ('16:00', '17:00')],
        'Wednesday': [('9:30', '11:30'), ('12:30', '14:00'), ('14:30', '15:30'), ('16:30', '17:00')]
    }

    days = ['Monday', 'Tuesday', 'Wednesday']

    for day in days:
        # Convert busy intervals to minutes and merge overlapping intervals
        intervals = []
        for interval in roy_busy[day]:
            start_min = time_str_to_minutes(interval[0])
            end_min = time_str_to_minutes(interval[1])
            intervals.append((start_min, end_min))
        
        # Sort intervals by start time
        intervals.sort(key=lambda x: x[0])
        merged = []
        for interval in intervals:
            if not merged:
                merged.append(interval)
            else:
                last = merged[-1]
                if interval[0] <= last[1]:
                    merged[-1] = (last[0], max(last[1], interval[1]))
                else:
                    merged.append(interval)
        
        # Calculate free intervals within work hours
        free_intervals = []
        current_start = work_start
        for interval in merged:
            if current_start < interval[0]:
                free_intervals.append((current_start, interval[0]))
            current_start = max(current_start, interval[1])
        if current_start < work_end:
            free_intervals.append((current_start, work_end))
        
        # Check each free interval for a slot of meeting_duration
        for interval in free_intervals:
            start, end = interval
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                # Convert to HH:MM strings
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                # Format as HH:MM:HH:MM
                s_h, s_m = start_str.split(':')
                e_h, e_m = end_str.split(':')
                print(day)
                print(f"{s_h}:{s_m}:{e_h}:{e_m}")
                return

if __name__ == "__main__":
    main()