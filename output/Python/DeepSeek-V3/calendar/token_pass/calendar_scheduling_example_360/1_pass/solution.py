def schedule_meeting():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Convert schedules to minutes since midnight
    schedules = {
        "Emily": [(10*60, 10*60+30), (16*60, 16*60+30)],
        "Mason": [],
        "Maria": [(10*60+30, 11*60), (14*60, 14*60+30)],
        "Carl": [(9*60+30, 10*60), (10*60+30, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
        "David": [(9*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 15*60), (16*60, 17*60)],
        "Frank": [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60+30), (14*60+30, 17*60)]
    }

    # Combine all busy times
    all_busy = []
    for person in schedules:
        all_busy.extend(schedules[person])
    
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])

    # Merge overlapping intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append([start, end])
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                merged_busy[-1][1] = max(last_end, end)
            else:
                merged_busy.append([start, end])

    # Find free slots within work hours
    free_slots = []
    current_time = work_start
    
    for busy_start, busy_end in merged_busy:
        if busy_start > current_time:
            free_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    
    if current_time < work_end:
        free_slots.append((current_time, work_end))

    # Find first free slot that can fit the meeting
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration:
            # Found a suitable slot
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            
            # Convert back to HH:MM format
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours:02d}:{mins:02d}"
            
            start_str = to_time_str(meeting_start)
            end_str = to_time_str(meeting_end)
            
            print(f"Monday:{start_str}:{end_str}")
            return
    
    print("No suitable time found")

if __name__ == "__main__":
    schedule_meeting()