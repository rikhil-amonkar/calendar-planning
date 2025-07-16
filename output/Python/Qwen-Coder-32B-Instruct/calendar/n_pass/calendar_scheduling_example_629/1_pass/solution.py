from datetime import datetime, timedelta

def find_meeting_time(margaret_schedule, alexis_schedule, meeting_duration, preferred_day, preferred_start_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    def parse_schedule(schedule):
        parsed_schedule = []
        for entry in schedule:
            start, end = entry.split(" to ")
            start_time = datetime.strptime(start, "%H:%M")
            end_time = datetime.strptime(end, "%H:%M")
            parsed_schedule.append((start_time, end_time))
        return parsed_schedule
    
    margaret_schedule = parse_schedule(margaret_schedule)
    alexis_schedule = parse_schedule(alexis_schedule)
    
    def is_time_slot_available(time_slot, schedule):
        for start, end in schedule:
            if not (time_slot[1] <= start or time_slot[0] >= end):
                return False
        return True
    
    def find_common_free_time(schedule1, schedule2, duration, preferred_day, preferred_start_time):
        current_time = datetime.strptime(f"{preferred_day} {preferred_start_time}", "%A %H:%M")
        while current_time + duration < work_end:
            time_slot = (current_time, current_time + duration)
            if is_time_slot_available(time_slot, schedule1) and is_time_slot_available(time_slot, schedule2):
                return time_slot
            current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
        return None
    
    common_free_time = find_common_free_time(margaret_schedule, alexis_schedule, meeting_duration, preferred_day, preferred_start_time)
    
    if common_free_time:
        start_time, end_time = common_free_time
        print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {preferred_day}")
    else:
        print("No available time slot found.")

# Given constraints
margaret_schedule = ["10:30 to 11:00", "11:30 to 12:00", "13:00 to 13:30", "15:00 to 17:00"]
alexis_schedule = ["9:30 to 11:30", "12:30 to 13:00", "14:00 to 17:00", "9:00 to 9:30", "10:00 to 10:30", "14:00 to 16:30"]
meeting_duration = 30  # in minutes
preferred_day = "Tuesday"
preferred_start_time = "12:30"

find_meeting_time(margaret_schedule, alexis_schedule, meeting_duration, preferred_day, preferred_start_time)