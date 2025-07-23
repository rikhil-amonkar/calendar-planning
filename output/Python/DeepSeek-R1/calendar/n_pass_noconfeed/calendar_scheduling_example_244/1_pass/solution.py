def main():
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 9 * 60  # 540
    work_end = 17 * 60   # 1020
    meeting_duration = 30

    # Busy intervals for each participant in minutes
    intervals = []
    
    # Cynthia
    intervals.append((9*60, 9*60+30))      # 9:00-9:30
    intervals.append((10*60, 10*60+30))    # 10:00-10:30
    intervals.append((13*60+30, 14*60+30)) # 13:30-14:30
    intervals.append((15*60, 16*60))       # 15:00-16:00
    
    # Ann
    intervals.append((10*60, 11*60))       # 10:00-11:00
    intervals.append((13*60, 13*60+30))    # 13:00-13:30
    intervals.append((14*60, 15*60))       # 14:00-15:00
    intervals.append((16*60, 16*60+30))    # 16:00-16:30
    
    # Catherine
    intervals.append((9*60, 11*60+30))     # 9:00-11:30
    intervals.append((12*60+30, 13*60+30)) # 12:30-13:30
    intervals.append((14*60+30, 17*60))    # 14:30-17:00
    
    # Kyle
    intervals.append((9*60, 9*60+30))      # 9:00-9:30
    intervals.append((10*60, 11*60+30))    # 10:00-11:30
    intervals.append((12*60, 12*60+30))    # 12:00-12:30
    intervals.append((13*60, 14*60+30))    # 13:00-14:30
    intervals.append((15*60, 16*60))       # 15:00-16:00
    
    # Walter: no meetings, so no intervals to add

    # Sort intervals by start time
    intervals.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    if intervals:
        merged = [intervals[0]]
        for i in range(1, len(intervals)):
            current_start, current_end = intervals[i]
            last_merged_start, last_merged_end = merged[-1]
            if current_start <= last_merged_end:
                # Overlapping or adjacent: merge
                merged[-1] = (last_merged_start, max(last_merged_end, current_end))
            else:
                merged.append((current_start, current_end))
    
    # Now find the earliest free slot of 30 minutes
    current = work_start
    meeting_start = None
    for interval in merged:
        interval_start, interval_end = interval
        if interval_start - current >= meeting_duration:
            meeting_start = current
            meeting_end = current + meeting_duration
            break
        else:
            current = interval_end
    else:
        # After the last interval
        if work_end - current >= meeting_duration:
            meeting_start = current
            meeting_end = current + meeting_duration
    
    # Convert meeting_start and meeting_end to HH:MM format
    def format_minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    if meeting_start is None:
        print("No suitable time found")
    else:
        start_time_str = format_minutes_to_time(meeting_start)
        end_time_str = format_minutes_to_time(meeting_end)
        # Format as HH:MM:HH:MM
        output_time = f"{start_time_str}:{end_time_str}"
        print("Monday", output_time)

if __name__ == "__main__":
    main()