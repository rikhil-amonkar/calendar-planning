from datetime import datetime, timedelta

def find_meeting_time(amanda_schedule, nathan_schedule, meeting_duration, constraints):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    def parse_schedule(schedule):
        parsed = []
        for entry in schedule:
            start, end = entry.split('-')
            start_time = datetime.strptime(start, "%H:%M")
            end_time = datetime.strptime(end, "%H:%M")
            parsed.append((start_time, end_time))
        return parsed
    
    amanda_schedule = parse_schedule(amanda_schedule)
    nathan_schedule = parse_schedule(nathan_schedule)
    
    def is_time_slot_free(schedule, time_slot):
        for event in schedule:
            if not (time_slot[1] <= event[0] or time_slot[0] >= event[1]):
                return False
        return True
    
    def generate_time_slots(start, end, duration):
        current = start
        while current + duration <= end:
            yield (current, current + duration)
            current += timedelta(minutes=30)
    
    for day in ["Monday", "Tuesday"]:
        if day == "Monday" and "Monday" in constraints and constraints["Monday"] == "off":
            continue
        if day == "Tuesday" and "Tuesday" in constraints and constraints["Tuesday"] == "off":
            continue
        
        amanda_availability = [slot for slot in generate_time_slots(work_start, work_end, timedelta(minutes=30)) if is_time_slot_free(amanda_schedule, slot)]
        nathan_availability = [slot for slot in generate_time_slots(work_start, work_end, timedelta(minutes=30)) if is_time_slot_free(nathan_schedule, slot)]
        
        common_availability = set(amanda_availability).intersection(set(nathan_availability))
        
        for slot in common_availability:
            if day == "Tuesday" and slot[0].hour > 11:
                continue
            return f"{slot[0].strftime('%H:%M')}:{slot[1].strftime('%H:%M')}", day

amanda_schedule = ["09:00-10:30", "11:00-11:30", "12:30-13:00", "13:30-14:00", "14:30-15:00"]
nathan_schedule = ["10:00-10:30", "11:00-11:30", "13:30-14:30", "16:00-16:30"]
meeting_duration = timedelta(minutes=30)
constraints = {"Monday": "off", "Tuesday": "before 11:00"}

meeting_time, meeting_day = find_meeting_time(amanda_schedule, nathan_schedule, meeting_duration, constraints)
print(f"{meeting_time}, {meeting_day}")