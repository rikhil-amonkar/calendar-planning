def main():
    # Convert work hours to minutes (9:00 to 17:00)
    work_start_minutes = 9 * 60   # 540 minutes
    work_end_minutes = 17 * 60    # 1020 minutes

    # Meeting must end by 12:30 (750 minutes from midnight)
    meeting_end_deadline = 12 * 60 + 30  # 750 minutes

    # Jack's busy time intervals (in minutes)
    jack_busy = [
        (9*60+30, 10*60+30),   # 09:30-10:30
        (11*60, 11*60+30),      # 11:00-11:30
        (12*60+30, 13*60),      # 12:30-13:00
        (14*60, 14*60+30),      # 14:00-14:30
        (16*60, 16*60+30)       # 16:00-16:30
    ]

    # Charlotte's busy time intervals (in minutes)
    charlotte_busy = [
        (9*60+30, 10*60),       # 09:30-10:00
        (10*60+30, 12*60),      # 10:30-12:00
        (12*60+30, 13*60+30),   # 12:30-13:30
        (14*60, 16*60)          # 14:00-16:00
    ]

    # Combine and sort all busy intervals
    all_busy = jack_busy + charlotte_busy
    all_busy.sort(key=lambda interval: interval[0])

    # Merge overlapping or adjacent busy intervals
    merged_busy = []
    if all_busy:
        current_start, current_end = all_busy[0]
        for start, end in all_busy[1:]:
            if start <= current_end:
                # Merge overlapping intervals
                current_end = max(current_end, end)
            else:
                # End of current merged interval
                merged_busy.append((current_start, current_end))
                current_start, current_end = start, end
        merged_busy.append((current_start, current_end))

    # Calculate free intervals within work hours
    free_intervals = []
    if not merged_busy:
        # Entire work day is free if no busy intervals
        free_intervals.append((work_start_minutes, work_end_minutes))
    else:
        # Check for free time before first busy interval
        if work_start_minutes < merged_busy[0][0]:
            free_intervals.append((work_start_minutes, merged_busy[0][0]))
        
        # Check for free time between busy intervals
        for i in range(len(merged_busy) - 1):
            current_end = merged_busy[i][1]
            next_start = merged_busy[i+1][0]
            if current_end < next_start:
                free_intervals.append((current_end, next_start))
        
        # Check for free time after last busy interval
        if merged_busy[-1][1] < work_end_minutes:
            free_intervals.append((merged_busy[-1][1], work_end_minutes))

    # Find earliest 30-minute meeting slot ending by 12:30
    meeting_slot = None
    for start, end in free_intervals:
        # Latest possible end time for this interval (considering 12:30 deadline)
        latest_possible_end = min(end, meeting_end_deadline)
        # Check if we can fit a 30-minute meeting
        if latest_possible_end - start >= 30:
            meeting_slot = (start, start + 30)
            break

    # Convert minutes to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Output results
    if meeting_slot:
        start_time = format_time(meeting_slot[0])
        end_time = format_time(meeting_slot[1])
        print(f"{start_time}:{end_time}")
        print("Monday")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()