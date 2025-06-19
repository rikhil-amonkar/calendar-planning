def main():
    # Meeting duration in minutes
    meeting_duration = 30
    # Work hours: 9:00 to 17:00, but Jose constraint: meeting must end by 15:30 (390 minutes from 9:00)
    work_start = 0      # 9:00 in minutes from 9:00
    jose_end = 390      # 15:30 in minutes from 9:00 (15:30 - 9:00 = 6.5 hours = 390 minutes)

    # Define busy intervals for each participant in minutes (start, end) relative to 9:00
    # Clip intervals to [0, 390] for Jose's constraint
    busy_intervals = []
    
    # Jose
    busy_intervals.append((120, 150))  # 11:00-11:30
    busy_intervals.append((210, 240))  # 12:30-13:00
    
    # Keith
    busy_intervals.append((300, 330))  # 14:00-14:30
    busy_intervals.append((360, 390))  # 15:00-15:30
    
    # Logan
    busy_intervals.append((0, 60))     # 9:00-10:00
    busy_intervals.append((180, 210))  # 12:00-12:30
    busy_intervals.append((360, 390))  # 15:00-15:30
    
    # Megan
    busy_intervals.append((0, 90))     # 9:00-10:30
    busy_intervals.append((120, 180))  # 11:00-12:00
    busy_intervals.append((240, 270))  # 13:00-13:30
    busy_intervals.append((330, 390))  # 14:30-16:30 clipped to 14:30-15:30
    
    # Gary
    busy_intervals.append((0, 30))     # 9:00-9:30
    busy_intervals.append((60, 90))    # 10:00-10:30
    busy_intervals.append((150, 240))  # 11:30-13:00
    busy_intervals.append((270, 300))  # 13:30-14:00
    busy_intervals.append((330, 390))  # 14:30-16:30 clipped to 14:30-15:30
    
    # Bobby
    busy_intervals.append((120, 150))  # 11:00-11:30
    busy_intervals.append((180, 210))  # 12:00-12:30
    busy_intervals.append((240, 390))  # 13:00-16:00 clipped to 13:00-15:30

    # Merge busy intervals
    if not busy_intervals:
        merged = []
    else:
        busy_intervals.sort(key=lambda x: x[0])
        merged = []
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
    
    # Find free intervals within [work_start, jose_end] that are at least meeting_duration
    free_intervals = []
    current_time = work_start
    for start, end in merged:
        if current_time < start:
            gap = start - current_time
            if gap >= meeting_duration:
                free_intervals.append((current_time, start))
        current_time = max(current_time, end)
    if current_time < jose_end:
        gap = jose_end - current_time
        if gap >= meeting_duration:
            free_intervals.append((current_time, jose_end))
    
    # Take the first free interval and schedule the meeting at the beginning
    if not free_intervals:
        # According to the problem, a solution exists, so this should not happen
        print("No suitable time found")
        return
    
    meeting_start = free_intervals[0][0]
    meeting_end_minutes = meeting_start + meeting_duration
    
    # Convert meeting_start and meeting_end_minutes to time strings (HH:MM format)
    def minutes_to_time(minutes):
        total_minutes = minutes
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end_minutes)
    
    # Format as HH:MM:HH:MM
    time_range_str = f"{start_str}:{end_str}".replace(':', '')  # Remove existing colons to avoid ambiguity
    # But the problem expects colons: so we break into parts and reassemble with colons
    # Since we have HHMMHHMM, we break into two parts: first 4 characters and last 4?
    # Instead, we format directly from the numbers:
    start_hour = 9 + meeting_start // 60
    start_min = meeting_start % 60
    end_hour = 9 + meeting_end_minutes // 60
    end_min = meeting_end_minutes % 60
    time_range_output = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    
    # Output day and time range
    print(f"Monday {time_range_output}")

if __name__ == "__main__":
    main()