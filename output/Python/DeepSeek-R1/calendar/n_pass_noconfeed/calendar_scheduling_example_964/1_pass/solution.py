def main():
    # Define work hours: 9:00 to 17:00 (8 hours = 480 minutes)
    work_start = 9 * 60  # 9:00 in minutes since midnight? But we use relative to 9:00.
    work_end = 17 * 60   # 17:00
    work_duration_minutes = work_end - work_start  # 480 minutes

    # Meeting duration: 1 hour = 60 minutes
    meeting_duration = 60

    # Betty cannot meet on Wednesday and Thursday
    allowed_days = ['Monday', 'Tuesday', 'Friday']

    # Define busy intervals for Betty and Megan for each day
    betty_busy = {
        'Monday': ['10:00-10:30', '11:30-12:30', '16:00-16:30'],
        'Tuesday': ['09:30-10:00', '10:30-11:00', '12:00-12:30', '13:30-15:00', '16:30-17:00'],
        'Wednesday': ['13:30-14:00', '14:30-15:00'],
        'Friday': ['09:00-10:00', '11:30-12:00', '12:30-13:00', '14:30-15:00']
    }

    megan_busy = {
        'Monday': ['09:00-17:00'],
        'Tuesday': ['09:00-09:30', '10:00-10:30', '12:00-14:00', '15:00-15:30', '16:00-16:30'],
        'Wednesday': ['09:30-10:30', '11:00-11:30', '12:30-13:00', '13:30-14:30', '15:30-17:00'],
        'Thursday': ['09:00-10:30', '11:30-14:00', '14:30-15:00', '15:30-16:30'],
        'Friday': ['09:00-17:00']
    }

    # Helper function to convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Iterate over allowed days
    found = False
    meeting_day = None
    meeting_start_min = None
    meeting_end_min = None

    for day in allowed_days:
        busy_intervals = []

        # Process Betty's busy intervals for the day
        if day in betty_busy:
            for interval in betty_busy[day]:
                start_str, end_str = interval.split('-')
                start_min = time_to_minutes(start_str)
                end_min = time_to_minutes(end_str)
                busy_intervals.append((start_min, end_min))

        # Process Megan's busy intervals for the day
        if day in megan_busy:
            for interval in megan_busy[day]:
                start_str, end_str = interval.split('-')
                start_min = time_to_minutes(start_str)
                end_min = time_to_minutes(end_str)
                busy_intervals.append((start_min, end_min))

        # If no busy intervals, the entire day is free
        if not busy_intervals:
            # Schedule at 9:00 (0 minutes since 9:00)
            meeting_start_min = 0
            meeting_end_min = meeting_start_min + meeting_duration
            meeting_day = day
            found = True
            break

        # Sort busy intervals by start time
        busy_intervals.sort(key=lambda x: x[0])

        # Merge overlapping or adjacent intervals
        merged = []
        current_start, current_end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= current_end:
                if e > current_end:
                    current_end = e
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))

        # Find gaps between merged intervals
        gaps = []
        # Check gap before first interval
        if merged[0][0] > 0:
            gaps.append((0, merged[0][0]))

        # Check gaps between intervals
        for i in range(len(merged) - 1):
            gap_start = merged[i][1]
            gap_end = merged[i+1][0]
            gaps.append((gap_start, gap_end))

        # Check gap after last interval
        if merged[-1][1] < work_duration_minutes:
            gaps.append((merged[-1][1], work_duration_minutes))

        # Check for a gap that can fit the meeting
        for gap in gaps:
            gap_start, gap_end = gap
            if gap_end - gap_start >= meeting_duration:
                meeting_start_min = gap_start
                meeting_end_min = gap_start + meeting_duration
                meeting_day = day
                found = True
                break  # Found a slot, break out of gap loop

        if found:
            break  # Found a slot, break out of day loop

    # Convert meeting start and end minutes to HH:MM format
    def minutes_to_time(minutes):
        total_minutes = minutes
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return hour, minute

    start_hour, start_minute = minutes_to_time(meeting_start_min)
    end_hour, end_minute = minutes_to_time(meeting_end_min)

    # Format as HH:MM:HH:MM
    time_range_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"

    # Output the day and time range
    print(meeting_day)
    print(time_range_str)

if __name__ == "__main__":
    main()