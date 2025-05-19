def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30        # Meeting duration in minutes

    # Convert all blocked times to minutes
    blocked = {
        'Judy': [(13*60, 13*60+30), (16*60, 16*60+30)],
        'Olivia': [(10*60, 10*60+30), (12*60, 13*60), (14*60, 14*60+30)],
        'Eric': [],
        'Jacqueline': [(10*60, 10*60+30), (15*60, 15*60+30)],
        'Laura': [(9*60, 10*60), (10*60+30, 12*60), (13*60, 13*60+30), (14*60+30, 15*60), (15*60+30, 17*60)],
        'Tyler': [(9*60, 10*60), (11*60, 11*60+30), (12*60+30, 13*60), (14*60, 14*60+30), (15*60+30, 17*60)],
        'Lisa': [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (16*60, 17*60)]
    }

    # Combine all busy times across participants
    all_busy = []
    for person in blocked.values():
        all_busy.extend(person)

    # Create a timeline of available slots
    timeline = []
    current_time = work_start
    for start, end in sorted(all_busy + [(work_end, work_end)]):
        if current_time < start:
            timeline.append((current_time, start))
        current_time = max(current_time, end)

    # Find first available slot that fits duration
    for slot_start, slot_end in timeline:
        if slot_end - slot_start >= duration:
            # Convert back to HH:MM format
            start_h = slot_start // 60
            start_m = slot_start % 60
            end_time = slot_start + duration
            end_h = end_time // 60
            end_m = end_time % 60
            return f"Monday\n{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"

    return "No suitable time found"

print(find_meeting_time())