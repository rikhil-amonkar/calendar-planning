def main():
    # Work hours: 9:00 to 17:00
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Collect all busy intervals (in minutes) from every participant
    busy_intervals = []
    
    # Jacob's busy times
    busy_intervals.append((13*60 + 30, 14*60))      # 13:30-14:00
    busy_intervals.append((14*60 + 30, 15*60))      # 14:30-15:00

    # Diana's busy times
    busy_intervals.append((9*60 + 30, 10*60))       # 9:30-10:00
    busy_intervals.append((11*60 + 30, 12*60))      # 11:30-12:00
    busy_intervals.append((13*60, 13*60 + 30))      # 13:00-13:30
    busy_intervals.append((16*60, 16*60 + 30))      # 16:00-16:30

    # Adam's busy times
    busy_intervals.append((9*60 + 30, 10*60 + 30))  # 9:30-10:30
    busy_intervals.append((11*60, 12*60 + 30))      # 11:00-12:30
    busy_intervals.append((15*60 + 30, 16*60))      # 15:30-16:00

    # Angela's busy times
    busy_intervals.append((9*60 + 30, 10*60))       # 9:30-10:00
    busy_intervals.append((10*60 + 30, 12*60))      # 10:30-12:00
    busy_intervals.append((13*60, 15*60 + 30))      # 13:00-15:30
    busy_intervals.append((16*60, 16*60 + 30))      # 16:00-16:30

    # Dennis's busy times
    busy_intervals.append((9*60, 9*60 + 30))        # 9:00-9:30
    busy_intervals.append((10*60 + 30, 11*60 + 30)) # 10:30-11:30
    busy_intervals.append((13*60, 15*60))           # 13:00-15:00
    busy_intervals.append((16*60 + 30, 17*60))      # 16:30-17:00

    # Generate candidate meeting slots (each 30 minutes)
    candidate_slots = []
    current = work_start
    while current + meeting_duration <= work_end:
        slot = (current, current + meeting_duration)
        candidate_slots.append(slot)
        current += 30

    # Find the first slot that doesn't overlap with any busy interval
    for slot in candidate_slots:
        s_start, s_end = slot
        overlap_found = False
        for (b_start, b_end) in busy_intervals:
            if s_start < b_end and b_start < s_end:
                overlap_found = True
                break
        if not overlap_found:
            # Convert slot to time strings
            s_hour = s_start // 60
            s_minute = s_start % 60
            e_hour = s_end // 60
            e_minute = s_end % 60
            # Format as HH:MM without leading zeros for hour
            start_str = f"{s_hour}:{s_minute:02d}"
            end_str = f"{e_hour}:{e_minute:02d}"
            # Output day and time range in HH:MM:HH:MM format
            print(f"Monday {start_str}:{end_str}")
            return

if __name__ == "__main__":
    main()