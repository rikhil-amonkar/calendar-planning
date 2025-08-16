from datetime import datetime, timedelta

def find_meeting_time(patricia_schedule, jesse_schedule, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    def parse_schedule(schedule):
        return [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), slot.split(' to '))) for slot in schedule]
    
    patricia_slots = parse_schedule(patricia_schedule)
    jesse_slots = parse_schedule(jesse_schedule)
    
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
    
    for day in ['Monday', 'Tuesday']:
        patricia_available = get_available_slots(patricia_slots, work_start, work_end)
        jesse_available = get_available_slots(jesse_slots, work_start, work_end)
        
        for pat_slot in patricia_available:
            for jess_slot in jesse_available:
                overlap_start = max(pat_slot[0], jess_slot[0])
                overlap_end = min(pat_slot[1], jess_slot[1])
                if (overlap_end - overlap_start) >= timedelta(hours=meeting_duration):
                    return f"{overlap_start.strftime('%H:%M')}:{overlap_end.strftime('%H:%M')}", day

patricia_schedule_monday = ["10:00 to 10:30", "11:30 to 12:00", "13:00 to 13:30", "14:30 to 15:30", "16:00 to 16:30"]
patricia_schedule_tuesday = ["10:00 to 10:30", "11:00 to 12:00", "14:00 to 16:00", "16:30 to 17:00"]
jesse_schedule_monday = ["9:00 to 17:00"]
jesse_schedule_tuesday = ["11:00 to 11:30", "12:00 to 12:30", "13:00 to 14:00", "14:30 to 15:00", "15:30 to 17:00"]

# Combine schedules for Monday and Tuesday
patricia_schedule = patricia_schedule_monday + patricia_schedule_tuesday
jesse_schedule = jesse_schedule_monday + jesse_schedule_tuesday

meeting_time, meeting_day = find_meeting_time(patricia_schedule, jesse_schedule, 1)
print(f"{meeting_time} on {meeting_day}")