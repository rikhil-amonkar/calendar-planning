from datetime import datetime, timedelta

def convert_to_minutes(time_str):
    """Converts time in HH:MM format to minutes since the start of the day."""
    return int(time_str[:2]) * 60 + int(time_str[3:])

def find_meeting_time():
    # Define work hours and meeting duration
    start_of_day = "09:00"
    end_of_day = "17:00"
    meeting_duration = 30  # in minutes
    
    # Convert work hours to minutes
    start_minutes = convert_to_minutes(start_of_day)
    end_minutes = convert_to_minutes(end_of_day)
    
    # Initialize availability dictionaries
    availability = {
        "Steven": [True] * (end_minutes - start_minutes),
        "Roy": [True] * (end_minutes - start_minutes),
        "Cynthia": [True] * (end_minutes - start_minutes),
        "Lauren": [True] * (end_minutes - start_minutes),
        "Robert": [True] * (end_minutes - start_minutes)
    }
    
    # Mark unavailable times for each participant
    def mark_unavailable(name, busy_times):
        for start, end in busy_times:
            start_min = convert_to_minutes(start) - start_minutes
            end_min = convert_to_minutes(end) - start_minutes
            for i in range(start_min, end_min):
                availability[name][i] = False
    
    # Define busy times for each participant
    mark_unavailable("Cynthia", [("09:30", "10:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("15:00", "16:00")])
    mark_unavailable("Lauren", [("09:00", "09:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), 
                                ("14:00", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")])
    mark_unavailable("Robert", [("10:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "16:00")])
    
    # Find the first time slot where all participants are available
    for start_min in range(end_minutes - start_minutes - meeting_duration + 1):
        if all(availability[name][start_min] for name in availability):
            # Convert start and end times back to HH:MM format
            start_time = (datetime.strptime(start_of_day, "%H:%M") + timedelta(minutes=start_min)).strftime("%H:%M")
            end_time = (datetime.strptime(start_of_day, "%H:%M") + timedelta(minutes=start_min + meeting_duration)).strftime("%H:%M")
            print(f"{start_time}:{end_time} Monday")
            return
    
    print("No available time slot found.")

find_meeting_time()