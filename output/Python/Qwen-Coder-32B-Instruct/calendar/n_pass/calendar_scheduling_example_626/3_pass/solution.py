from datetime import datetime, timedelta

def find_meeting_time(patricia_schedule_monday, patricia_schedule_tuesday, jesse_schedule_monday, jesse_schedule_tuesday, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    def parse_schedule(schedule):
        return [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), slot.split(' to '))) for slot in schedule]
    
    def get_available_slots(slots, start, end):
        available_slots = []
        current = start
        for slot in slots:
            if current < slot[0]:
                available_slots.append((current, slot[0]))
            current = max(current, slot[1])
        if current < end:
            available_slots.append((current, end))
        return available_slots
    
    # Parse schedules
    patricia_slots_monday = parse_schedule(patricia_schedule_monday)
    jesse_slots_monday = parse_schedule(jesse_schedule_monday)
    patricia_slots_tuesday = parse_schedule(patricia_schedule_tuesday)
    jesse_slots_tuesday = parse_schedule(jesse_schedule_tuesday)
    
    # Check for available time slots on Monday
    patricia_available_monday = get_available_slots(patricia_slots_monday, work_start, work_end)
    jesse_available_monday = get_available_slots(jesse_slots_monday, work_start, work_end)
    
    for pat_slot in patricia_available_monday:
        for jess_slot in jesse_available_monday:
            overlap_start = max(pat_slot[0], jess_slot[0])
            overlap_end = min(pat_slot[1], jess_slot[1])
            if (overlap_end - overlap_start) >= timedelta(hours=meeting_duration):
                return overlap_start.strftime('%H:%M'), (overlap_start + timedelta(hours=meeting_duration)).strftime('%H:%M'), 'Monday'
    
    # Check for available time slots on Tuesday
    patricia_available_tuesday = get_available_slots(patricia_slots_tuesday, work_start, work_end)
    jesse_available_tuesday = get_available_slots(jesse_slots_tuesday, work_start, work_end)
    
    for pat_slot in patricia_available_tuesday:
        for jess_slot in jesse_available_tuesday:
            overlap_start = max(pat_slot[0], jess_slot[0])
            overlap_end = min(pat_slot[1], jess_slot[1])
            if (overlap_end - overlap_start) >= timedelta(hours=meeting_duration):
                return overlap_start.strftime('%H:%M'), (overlap_start + timedelta(hours=meeting_duration)).strftime('%H:%M'), 'Tuesday'
    
    # Return a default value if no suitable meeting time is found
    return None, None, None

# Schedules for Monday and Tuesday
patricia_schedule_monday = ["10:00 to 10:30", "11:30 to 12:00", "13:00 to 13:30", "14:30 to 15:30", "16:00 to 16:30"]
patricia_schedule_tuesday = ["10:00 to 10:30", "11:00 to 12:00", "14:00 to 16:00", "16:30 to 17:00"]
jesse_schedule_monday = ["9:00 to 17:00"]
jesse_schedule_tuesday = ["11:00 to 11:30", "12:00 to 12:30", "13:00 to 14:00", "14:30 to 15:00", "15:30 to 17:00"]

meeting_start, meeting_end, meeting_day = find_meeting_time(
    patricia_schedule_monday, patricia_schedule_tuesday,
    jesse_schedule_monday, jesse_schedule_tuesday,
    1
)

if meeting_start is not None:
    print(f"Meeting from {meeting_start} to {meeting_end} on {meeting_day}")
else:
    print("No suitable meeting time found.")