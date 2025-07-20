def main():
    # Work hours: 9:00 to 17:00 (8 hours = 480 minutes)
    work_start_min = 9 * 60  # 540 minutes from midnight
    work_end_min = 17 * 60   # 1020 minutes from midnight
    duration_min = 30        # meeting duration

    # Timeline array: 480 minutes (from 9:00 to 17:00), index 0 = 9:00, index 479 = 16:59
    timeline = [True] * (work_end_min - work_start_min)  # 480 elements, initially all free

    # Define busy intervals for each participant as (start, end) in time strings
    diane = [("9:30", "10:00"), ("14:30", "15:00")]
    jack = [("13:30", "14:00"), ("14:30", "15:00")]
    eugene = [("9:00", "10:00"), ("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "16:30")]
    patricia = [("9:30", "10:30"), ("11:00", "12:00"), ("12:30", "14:00"), ("15:00", "16:30")]
    participants = [diane, jack, eugene, patricia]

    # Helper function to convert "HH:MM" to minutes from midnight
    def time_str_to_minutes(time_str):
        h, m = time_str.split(':')
        return int(h) * 60 + int(m)

    # Mark busy intervals on the timeline
    for person in participants:
        for interval in person:
            start_str, end_str = interval
            start_min = time_str_to_minutes(start_str)
            end_min = time_str_to_minutes(end_str)
            
            # Only consider intervals within work hours
            if end_min <= work_start_min or start_min >= work_end_min:
                continue
                
            # Calculate start and end indices in the timeline array
            start_idx = max(0, start_min - work_start_min)
            end_idx = min(len(timeline), end_min - work_start_min)
            
            # Mark the interval as busy (False)
            for i in range(start_idx, end_idx):
                timeline[i] = False

    # Find the earliest 30-minute free slot
    found = False
    start_index = -1
    for i in range(len(timeline) - duration_min + 1):
        if all(timeline[i:i + duration_min]):
            start_index = i
            found = True
            break

    if not found:
        print("No suitable time found")
        return

    # Convert start index to minutes from midnight and then to time string
    start_total_min = work_start_min + start_index
    end_total_min = start_total_min + duration_min

    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    start_time_str = format_time(start_total_min)
    end_time_str = format_time(end_total_min)

    # Output the day and time range in specified format
    print(f"Monday {start_time_str}:{end_time_str}")

if __name__ == "__main__":
    main()