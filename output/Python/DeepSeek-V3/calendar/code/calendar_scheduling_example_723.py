from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours and days to consider
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    days = ["Monday", "Tuesday", "Wednesday"]
    
    # Define participants' schedules and constraints
    arthur_schedule = {
        "Monday": [
            ("11:00", "11:30"),
            ("13:30", "14:00"),
            ("15:00", "15:30")
        ],
        "Tuesday": [
            ("13:00", "13:30"),
            ("16:00", "16:30")
        ],
        "Wednesday": [
            ("10:00", "10:30"),
            ("11:00", "11:30"),
            ("12:00", "12:30"),
            ("14:00", "14:30"),
            ("16:00", "16:30")
        ]
    }
    
    michael_schedule = {
        "Monday": [
            ("09:00", "12:00"),
            ("12:30", "13:00"),
            ("14:00", "14:30"),
            ("15:00", "17:00")
        ],
        "Tuesday": [
            ("09:30", "11:30"),
            ("12:00", "13:30"),
            ("14:00", "15:30")
        ],
        "Wednesday": [
            ("10:00", "12:30"),
            ("13:00", "13:30")
        ]
    }
    
    # Arthur cannot meet on Tuesday
    days_to_check = [day for day in days if day != "Tuesday"]
    
    # Iterate through each day to find the earliest available slot
    for day in days_to_check:
        # Combine and sort all meetings for the day for both participants
        all_meetings = []
        
        # Add Arthur's meetings
        for meeting in arthur_schedule.get(day, []):
            start = datetime.strptime(meeting[0], "%H:%M")
            end = datetime.strptime(meeting[1], "%H:%M")
            all_meetings.append((start, end))
        
        # Add Michael's meetings
        for meeting in michael_schedule.get(day, []):
            start = datetime.strptime(meeting[0], "%H:%M")
            end = datetime.strptime(meeting[1], "%H:%M")
            all_meetings.append((start, end))
        
        # Sort meetings by start time
        all_meetings.sort()
        
        # Check for available slots
        prev_end = work_start
        for meeting in all_meetings:
            meeting_start, meeting_end = meeting
            if meeting_start > prev_end:
                # Check if the gap is at least 30 minutes
                gap = (meeting_start - prev_end).total_seconds() / 60
                if gap >= 30:
                    # Found a suitable slot
                    slot_start = prev_end
                    slot_end = slot_start + timedelta(minutes=30)
                    return day, slot_start.time(), slot_end.time()
            # Update prev_end to the later of the two
            prev_end = max(prev_end, meeting_end)
        
        # Check after the last meeting
        if prev_end < work_end:
            gap = (work_end - prev_end).total_seconds() / 60
            if gap >= 30:
                slot_start = prev_end
                slot_end = slot_start + timedelta(minutes=30)
                return day, slot_start.time(), slot_end.time()
    
    return None

# Find the meeting time
result = find_meeting_time()
if result:
    day, start_time, end_time = result
    # Format the output as HH:MM:HH:MM and day
    start_str = start_time.strftime("%H:%M")
    end_str = end_time.strftime("%H:%M")
    print(f"{day}: {start_str}:{end_str}")
else:
    print("No suitable time found.")