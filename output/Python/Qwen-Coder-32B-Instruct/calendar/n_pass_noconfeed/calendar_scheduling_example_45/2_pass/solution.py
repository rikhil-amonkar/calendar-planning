from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert times to minutes since start of the day for easier calculations
    work_start_minutes = work_start.hour * 60 + work_start.minute
    work_end_minutes = work_end.hour * 60 + work_end.minute
    meeting_duration_minutes = meeting_duration.seconds // 60
    
    # Function to convert minutes since start of the day to datetime object
    def minutes_to_datetime(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return datetime.strptime(f"{hours}:{minutes}", "%H:%M")
    
    # Initialize available time slots for each person
    available_slots_per_person = {}
    
    # Check each participant's schedule
    for person, busy_times in schedules.items():
        current_time = work_start_minutes
        available_slots = []
        
        for start, end in busy_times:
            start_minutes = start.hour * 60 + start.minute
            end_minutes = end.hour * 60 + end.minute
            
            # Add free time slot before the next busy period
            if current_time < start_minutes:
                available_slots.append((current_time, min(end_minutes, work_end_minutes)))
            
            # Update current time to the end of the busy period
            current_time = max(current_time, end_minutes)
        
        # Add free time slot after the last busy period if any
        if current_time < work_end_minutes:
            available_slots.append((current_time, work_end_minutes))
        
        available_slots_per_person[person] = available_slots
    
    # Find common available time slot
    common_slots = None
    
    for person, slots in available_slots_per_person.items():
        if common_slots is None:
            common_slots = slots[:]
        else:
            new_common_slots = []
            for start1, end1 in common_slots:
                for start2, end2 in slots:
                    start_common = max(start1, start2)
                    end_common = min(end1, end2)
                    if start_common + meeting_duration_minutes <= end_common:
                        new_common_slots.append((start_common, end_common))
            common_slots = new_common_slots
        
        # If at any point there are no common slots, break early
        if not common_slots:
            break
    
    # Convert back to HH:MM format
    if common_slots:
        for start_minutes, end_minutes in common_slots:
            if start_minutes + meeting_duration_minutes <= end_minutes:
                start_time = minutes_to_datetime(start_minutes)
                end_time = start_time + timedelta(minutes=meeting_duration_minutes)
                return f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}, Monday"
    
    return "No common time slot found"

# Define the schedules and constraints
schedules = {
    'Andrew': [],
    'Grace': [],
    'Samuel': [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Find and print the meeting time
print(find_meeting_time(schedules, meeting_duration, work_start, work_end))