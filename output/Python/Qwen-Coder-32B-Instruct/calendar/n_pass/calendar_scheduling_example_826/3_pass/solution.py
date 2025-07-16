from datetime import datetime, timedelta

def find_meeting_time(cheryl_schedule, james_schedule, preferred_days, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert schedules to datetime objects
    def convert_to_datetime(schedule):
        return {(day, datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for day, start, end in schedule}
    
    cheryl_schedule = convert_to_datetime(cheryl_schedule)
    james_schedule = convert_to_datetime(james_schedule)
    
    # Function to check if two time intervals overlap
    def intervals_overlap(interval1, interval2):
        return interval1[1] > interval2[0] and interval2[1] > interval1[0]
    
    # Check available times for each day
    for day in preferred_days:
        current_time = work_start
        
        while current_time + timedelta(minutes=meeting_duration) <= work_end:
            meeting_start = current_time
            meeting_end = meeting_start + timedelta(minutes=meeting_duration)
            meeting_interval = (meeting_start, meeting_end)
            
            # Check if this meeting interval overlaps with any of James's or Cheryl's busy intervals
            busy_intervals = [interval for d, start, end in james_schedule if d == day and intervals_overlap((start, end), meeting_interval)] + \
                             [interval for d, start, end in cheryl_schedule if d == day and intervals_overlap((start, end), meeting_interval)]
            
            if not busy_intervals:
                # No overlap found, this is a valid meeting time
                return meeting_start.strftime('%H:%M'), day
            
            # Move current_time to the end of the latest overlapping interval
            current_time = max(interval[1] for interval in busy_intervals)
    
    return None, None  # No available time found

# Cheryl's schedule
cheryl_schedule = [
    ("Monday", "09:00", "10:00"), ("Monday", "11:00", "12:00"), ("Monday", "13:00", "14:00"), ("Monday", "15:00", "16:00"),
    ("Tuesday", "09:30", "10:30"), ("Tuesday", "11:30", "12:30"), ("Tuesday", "13:30", "14:30"), ("Tuesday", "15:30", "16:30")
]

# James's schedule
james_schedule = [
    ("Monday", "09:00", "09:30"), ("Monday", "10:30", "11:00"), ("Monday", "12:30", "13:00"), ("Monday", "14:30", "15:30"), ("Monday", "16:30", "17:00"),
    ("Tuesday", "09:00", "11:00"), ("Tuesday", "11:30", "12:00"), ("Tuesday", "12:30", "15:30"), ("Tuesday", "16:00", "17:00")
]

# Preferred days excluding Wednesday and Thursday
preferred_days = ["Monday", "Tuesday"]

# Meeting duration in minutes
meeting_duration = 30

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time(cheryl_schedule, james_schedule, preferred_days, meeting_duration)
if meeting_time:
    print(f"{meeting_time}, {meeting_day}")
else:
    print("No available time found.")