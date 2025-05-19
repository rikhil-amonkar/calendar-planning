def find_meeting_time():
    work_hours = (9*60, 17*60)  # 9:00 to 17:00 in minutes
    duration = 30
    participants = {
        'Tyler': [],
        'Kelly': [],
        'Stephanie': [(11*60, 11*60+30), (14*60+30, 15*60)],
        'Hannah': [],
        'Joe': [(9*60, 9*60+30), (10*60, 12*60), (12*60+30, 13*60), (14*60, 17*60)],
        'Diana': [(9*60, 10*60+30), (11*60+30, 12*60), (13*60, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
        'Deborah': [(9*60, 10*60), (10*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 16*60+30)]
    }

    # Convert all busy slots to minutes and merge
    all_busy = []
    for person in participants.values():
        all_busy.extend(person)
    all_busy.sort()

    # Find free slots by checking gaps between busy times and work hours
    free_slots = []
    prev_end = work_hours[0]
    for start, end in all_busy + [(work_hours[1], work_hours[1])]:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    # Find first suitable slot
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            def time_str(minutes):
                return f"{minutes//60:02d}:{minutes%60:02d}"
            return f"Monday {time_str(meeting_start)}-{time_str(meeting_end)}"

print(find_meeting_time())