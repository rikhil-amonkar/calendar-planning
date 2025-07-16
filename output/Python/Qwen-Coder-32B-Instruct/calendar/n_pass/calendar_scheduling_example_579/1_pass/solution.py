from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert work hours to datetime objects
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Iterate over each participant's schedule
    for participant, schedule in participants.items():
        current_time = work_start
        
        # Add initial free slot before first meeting
        if schedule[0][0] > work_start:
            available_slots.append((current_time, schedule[0][0]))
        
        # Add free slots between meetings
        for i in range(len(schedule) - 1):
            if schedule[i][1] < schedule[i + 1][0]:
                available_slots.append((schedule[i][1], schedule[i + 1][0]))
        
        # Add free slot after last meeting
        if schedule[-1][1] < work_end:
            available_slots.append((schedule[-1][1], work_end))
    
    # Find common free slots that fit the meeting duration
    common_slots = []
    for slot in available_slots:
        if slot[1] - slot[0] >= timedelta(minutes=meeting_duration):
            common_slots.append(slot)
    
    # Check for a time that works for all participants
    for slot in common_slots:
        works_for_all = True
        for participant, schedule in participants.items():
            for meeting in schedule:
                if slot[0] < meeting[1] and slot[1] > meeting[0]:
                    works_for_all = False
                    break
            if not works_for_all:
                break
        if works_for_all:
            return f"{slot[0].strftime('%H:%M')}:{slot[1].strftime('%H:%M')}", "Monday"
    
    return None, None

# Define participants' schedules
participants = {
    "Christine": [
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))
    ],
    "Helen": [
        (datetime.strptime("9:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Meeting details
meeting_duration = 30  # in minutes
work_start = "9:00"
work_end = "17:00"

# Find and print the meeting time
meeting_time, day = find_meeting_time(participants, meeting_duration, work_start, work_end)
print(f"{meeting_time}:{day}")