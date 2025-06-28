def main():
    # Work hours: 9:00 to 17:00 (in minutes from midnight)
    work_start = 9 * 60   # 540 minutes
    work_end = 17 * 60    # 1020 minutes

    # Jennifer's busy intervals per day (each as (start_minute, end_minute))
    jennifer_busy = {
        'Monday': [
            (9*60, 11*60),          # 9:00-11:00
            (11*60+30, 13*60),      # 11:30-13:00
            (13*60+30, 14*60+30),   # 13:30-14:30
            (15*60, 17*60)          # 15:00-17:00
        ],
        'Tuesday': [
            (9*60, 11*60+30),       # 9:00-11:30
            (12*60, 17*60)          # 12:00-17:00
        ],
        'Wednesday': [
            (9*60, 11*60+30),       # 9:00-11:30
            (12*60, 12*60+30),      # 12:00-12:30
            (13*60, 14*60),         # 13:00-14:00
            (14*60+30, 16*60),      # 14:30-16:00
            (16*60+30, 17*60)       # 16:30-17:00
        ]
    }

    days = ['Monday', 'Tuesday', 'Wednesday']
    candidate_found = False

    for day in days:
        # Get and sort busy intervals for the day
        busy_today = jennifer_busy[day]
        busy_today.sort(key=lambda x: x[0])
        
        # Calculate free intervals
        free_intervals = []
        current = work_start
        for start, end in busy_today:
            if current < start:
                free_intervals.append((current, start))
            current = max(current, end)
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check each free interval for a 30-minute slot
        for start, end in free_intervals:
            duration = end - start
            if duration >= 30:
                # Apply John's constraint: avoid Monday after 14:30 (870 minutes)
                if day == 'Monday' and start >= 14*60+30:
                    continue
                meeting_start = start
                meeting_end = start + 30
                if meeting_end <= end:  # Ensure the meeting fits
                    # Format the meeting time
                    start_hour = meeting_start // 60
                    start_minute = meeting_start % 60
                    end_hour = meeting_end // 60
                    end_minute = meeting_end % 60
                    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                    print(day)
                    print(time_str)
                    candidate_found = True
                    break  # Break inner loop
        if candidate_found:
            break  # Break outer loop after first candidate

    if not candidate_found:
        print("No meeting time found")

if __name__ == "__main__":
    main()