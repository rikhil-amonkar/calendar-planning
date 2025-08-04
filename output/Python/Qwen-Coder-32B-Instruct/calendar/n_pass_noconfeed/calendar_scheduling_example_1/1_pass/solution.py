from datetime import datetime, timedelta

def find_meeting_time(raymond_schedule, billy_schedule, donald_schedule, preferred_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=30)
    
    # Convert all times to datetime objects for easier comparison
    raymond_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in raymond_schedule]
    billy_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in billy_schedule]
    donald_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in donald_schedule]
    
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        current_end_time = current_time + meeting_duration
        if current_end_time > preferred_end_time:
            break
        
        # Check if the current time slot is free for all participants
        if (all(current_time < start or current_end_time > end for start, end in raymond_blocked_times) and
            all(current_time < start or current_end_time > end for start, end in billy_blocked_times) and
            all(current_time < start or current_end_time > end for start, end in donald_blocked_times)):
            
            return current_time.strftime("%H:%M"), current_end_time.strftime("%H:%M")
        
        current_time += timedelta(minutes=30)
    
    return None

# Schedules in the format of (start_time, end_time)
raymond_schedule = [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("15:00", "15:30")]
billy_schedule = [("10:00", "10:30"), ("12:00", "13:00"), ("16:30", "17:00")]
donald_schedule = [("09:00", "09:30"), ("10:00", "11:00"), ("12:00", "13:00"), ("14:00", "14:30"), ("16:00", "17:00")]

preferred_end_time = datetime.strptime("15:00", "%H:%M")

meeting_start, meeting_end = find_meeting_time(raymond_schedule, billy_schedule, donald_schedule, preferred_end_time)

print(f"{meeting_start}:{meeting_end} Monday")