from datetime import datetime, timedelta

def find_meeting_time(cheryl_schedule, james_schedule, preferred_days, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert schedules to datetime objects
    def convert_to_datetime(schedule):
        return [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in schedule]
    
    james_schedule = convert_to_datetime(james_schedule)
    
    # Function to check if two time intervals overlap
    def intervals_overlap(interval1, interval2):
        return interval1[0] < interval2[1] and interval2[0] < interval1[1]
    
    # Check available times for each day
    for day in preferred_days:
        cheryl_busy = False  # Cheryl is free all day
        current_time = work_start
        
        while current_time + timedelta(minutes=meeting_duration) <= work_end:
            meeting_start = current_time
            meeting_end = meeting_start + timedelta(minutes=meeting_duration)
            meeting_interval = (meeting_start, meeting_end)
            
            # Check if this meeting interval overlaps with any of James's busy intervals
            for start, end in james_schedule:
                if intervals_overlap(meeting_interval, (start, end)):
                    # Move current_time to the end of the overlapping interval
                    current_time = end
                    break
            else:
                # No overlap found, this is a valid meeting time
                return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day
            
            # Move to the next possible meeting start time
            current_time += timedelta(minutes=1)
    
    return None, None  # No available time found

# James's schedule
james_schedule = [
    ("09:00", "09:30"), ("10:30", "11:00"), ("12:30", "13:00"), ("14:30", "15:30"), ("16:30", "17:00"),
    ("09:00", "11:00"), ("11:30", "12:00"), ("12:30", "15:30"), ("16:00", "17:00"),
    ("10:00", "11:00"), ("12:00", "13:00"), ("13:30", "16:00"),
    ("09:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")
]

# Preferred days excluding Wednesday and Thursday
preferred_days = ["Monday", "Tuesday"]

# Meeting duration in minutes
meeting_duration = 30

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time({}, james_schedule, preferred_days, meeting_duration)
if meeting_time:
    print(f"{meeting_time}, {meeting_day}")
else:
    print("No available time found.")