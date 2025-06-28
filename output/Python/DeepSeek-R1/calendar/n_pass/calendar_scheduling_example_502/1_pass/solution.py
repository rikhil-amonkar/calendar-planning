def main():
    work_start = 9 * 60  # 9:00 in minutes (540)
    work_end = 17 * 60   # 17:00 in minutes (1020)
    meeting_duration = 30  # minutes
    preference_cutoff = 12 * 60 + 30  # 12:30 in minutes (750)

    # Define busy intervals in minutes for each participant
    jack_busy = [
        (9*60+30, 10*60+30),  # 9:30-10:30
        (11*60, 11*60+30),     # 11:00-11:30
        (12*60+30, 13*60),     # 12:30-13:00
        (14*60, 14*60+30),     # 14:00-14:30
        (16*60, 16*60+30)      # 16:00-16:30
    ]
    
    charlotte_busy = [
        (9*60+30, 10*60),      # 9:30-10:00
        (10*60+30, 12*60),     # 10:30-12:00
        (12*60+30, 13*60+30),  # 12:30-13:30
        (14*60, 16*60)         # 14:00-16:00
    ]
    
    # Combine and sort all busy intervals
    all_busy = jack_busy + charlotte_busy
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if all_busy:
        start, end = all_busy[0]
        for s, e in all_busy[1:]:
            if s <= end:
                end = max(end, e)
            else:
                merged.append((start, end))
                start, end = s, e
        merged.append((start, end))
    
    # Find free time slots within work hours
    free_slots = []
    current = work_start
    
    for interval in merged:
        s, e = interval
        if current < s:
            gap_start = current
            gap_end = s
            if gap_end - gap_start >= meeting_duration:
                free_slots.append((gap_start, gap_end))
        current = max(current, e)
    
    # Check after the last busy interval
    if current < work_end:
        if work_end - current >= meeting_duration:
            free_slots.append((current, work_end))
    
    # Find the earliest slot that ends by the preference cutoff
    candidate = None
    for slot in free_slots:
        slot_start, slot_end = slot
        meeting_end = slot_start + meeting_duration
        if meeting_end <= slot_end and meeting_end <= preference_cutoff:
            candidate = (slot_start, meeting_end)
            break
    
    # If no slot meets the preference, find any available slot
    if candidate is None:
        for slot in free_slots:
            slot_start, slot_end = slot
            if slot_end - slot_start >= meeting_duration:
                candidate = (slot_start, slot_start + meeting_duration)
                break
    
    # Convert minutes to HH:MM format
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_time = format_time(candidate[0])
    end_time = format_time(candidate[1])
    time_range_str = f"{start_time}:{end_time}"
    
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()