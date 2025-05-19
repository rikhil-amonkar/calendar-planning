def find_meeting_time():
    # Define work hours and days to check
    work_start = 9 * 60
    work_end = 17 * 60
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_duration = 30

    # Ruth's schedule converted to minutes since midnight
    ruth_busy = {
        "Monday": [(9*60, 17*60)],
        "Tuesday": [(9*60, 17*60)],
        "Wednesday": [(9*60, 17*60)],
        "Thursday": [(9*60, 11*60), (11*60 + 30, 14*60 + 30), (15*60, 17*60)]
    }

    # Check available slots on Thursday first due to Julie's preference
    for day in ["Thursday", "Monday", "Tuesday", "Wednesday"]:
        if day not in days:
            continue
        
        # Get Ruth's busy periods for the day
        busy = ruth_busy.get(day, [])
        free_slots = []
        previous_end = work_start
        
        # Calculate free intervals between busy periods
        for start, end in sorted(busy):
            if start > previous_end:
                free_slots.append((previous_end, start))
            previous_end = max(previous_end, end)
        if previous_end < work_end:
            free_slots.append((previous_end, work_end))
        
        # Check Julie's Thursday preference
        if day == "Thursday":
            free_slots = [(s, e) for s, e in free_slots if s >= 11*60 + 30]
        
        # Find first available slot
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_day = day
                # Convert back to HH:MM format
                return (
                    f"{meeting_day} "
                    f"{meeting_start//60:02d}:{meeting_start%60:02d}:"
                    f"{(meeting_start + meeting_duration)//60:02d}:"
                    f"{(meeting_start + meeting_duration)%60:02d}"
                )

    return "No suitable time found"

print(find_meeting_time())