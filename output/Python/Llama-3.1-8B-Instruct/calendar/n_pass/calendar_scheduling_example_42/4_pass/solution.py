from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.
    
    Args:
    start_time (str): Start time of the work hours.
    end_time (str): End time of the work hours.
    meeting_duration (int): Duration of the meeting in minutes.
    schedules (dict): Dictionary of participant schedules.
    
    Returns:
    str: Proposed time in the format HH:MM-HH:MM.
    """
    
    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize proposed time
    proposed_time = start_time
    
    # Loop until we find a time that works for everyone
    while proposed_time < end_time:
        # Check if the proposed time works for each participant
        works_for_everyone = True
        for participant, schedule in schedules.items():
            for time in schedule:
                if proposed_time >= time[0] and proposed_time < time[1]:
                    # Check if the meeting time conflicts with the unavailable time slot
                    if (proposed_time.hour == 9 and proposed_time.minute >= 0 and proposed_time.minute < 30) or \
                       (proposed_time + timedelta(minutes=meeting_duration)).hour == 9 and proposed_time + timedelta(minutes=meeting_duration) >= time[0] and proposed_time + timedelta(minutes=meeting_duration) < time[1]:
                        works_for_everyone = False
                        break
                elif proposed_time == time[0] and proposed_time + timedelta(minutes=1) >= time[0] and proposed_time + timedelta(minutes=1) < time[1]:
                    # If the proposed time is the start of an unavailable time slot, skip it
                    works_for_everyone = False
                    break
        
        # If the proposed time works for everyone, return it
        if works_for_everyone:
            # Convert proposed time to string and format it as HH:MM-HH:MM
            proposed_time_str = proposed_time.strftime("%H:%M") + "-" + (proposed_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
            # Return the proposed time and the day of the week
            return f"{proposed_time_str} on {start_time.strftime('%A')}"
        
        # If the proposed time doesn't work for everyone, move to the next time
        proposed_time += timedelta(minutes=1)

# Define the schedules for each participant
schedules = {
    "Julie": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
              (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Sean": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Lori": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
             (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
             (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Find a time that works for everyone
meeting_duration = 60  # 1 hour
start_time = "09:00"
end_time = "17:00"
print(find_meeting_time(start_time, end_time, meeting_duration, schedules))