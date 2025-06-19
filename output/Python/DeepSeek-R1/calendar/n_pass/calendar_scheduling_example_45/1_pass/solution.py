def main():
    # Work hours: 9:00 to 17:00
    work_start_min = 9 * 60  # 540 minutes
    work_end_min = 17 * 60   # 1020 minutes

    # Samuel's busy times in minutes (start, end)
    busy_times = [
        (9*60, 10*60 + 30),   # 9:00 to 10:30
        (11*60 + 30, 12*60),   # 11:30 to 12:00
        (13*60, 13*60 + 30),   # 13:00 to 13:30
        (14*60, 16*60),        # 14:00 to 16:00
        (16*60 + 30, 17*60)    # 16:30 to 17:00
    ]

    # Sort busy times by start time
    busy_times.sort(key=lambda x: x[0])
    
    free_slots = []
    current_time = work_start_min
    
    for start_busy, end_busy in busy_times:
        if start_busy > current_time:
            free_slots.append((current_time, start_busy))
        if end_busy > current_time:
            current_time = end_busy
    
    if current_time < work_end_min:
        free_slots.append((current_time, work_end_min))
    
    meeting_start = None
    meeting_end = None
    for start_slot, end_slot in free_slots:
        slot_duration = end_slot - start_slot
        if slot_duration >= 30:
            meeting_start = start_slot
            meeting_end = start_slot + 30
            break
    
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    if meeting_start is not None:
        start_str = format_time(meeting_start)
        end_str = format_time(meeting_end)
        time_range_str = f"{start_str}:{end_str}"
        print(f"Monday {time_range_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()