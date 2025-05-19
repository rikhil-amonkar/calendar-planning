import json
from datetime import datetime, timedelta

# Define input variables
travel_times = {
    "Nob Hill to Presidio": 17,
    "Presidio to Nob Hill": 18
}
arrival_time_nob_hill = datetime.strptime("09:00", "%H:%M")
robert_start_time = datetime.strptime("11:15", "%H:%M")
robert_end_time = datetime.strptime("17:45", "%H:%M")  # Meeting can end at this time
meet_duration = timedelta(minutes=120)

# Calculate when you can leave Nob Hill to meet Robert
def calculate_schedule():
    # You need to arrive at Presidio before Robert can meet you
    travel_to_presidio = travel_times["Nob Hill to Presidio"]
    latest_time_to_leave_nob_hill = robert_start_time - timedelta(minutes=travel_to_presidio)
    
    # You can start meeting Robert after arriving at Presidio
    first_available_meeting_start = robert_start_time
    meeting_end_time = first_available_meeting_start + meet_duration

    meeting_times = []
    
    if latest_time_to_leave_nob_hill < first_available_meeting_start:
        # You cannot reach Robert in time before he starts meeting
        return meeting_times
    
    # Check if you can meet Robert all at once
    if meeting_end_time <= robert_end_time:
        start_presidio_meeting = first_available_meeting_start.strftime("%H:%M")
        end_presidio_meeting = meeting_end_time.strftime("%H:%M")
        meeting_times.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": start_presidio_meeting,
            "end_time": end_presidio_meeting
        })
        return meeting_times
    
    # If we cannot meet continuously for 120 minutes within the allowed time, we'll need to adjust
    # Check for possible shorter meetings that still meet the duration
    # Break down into two meetings if needed
    total_meeting_time = 0
    available_meeting_start = first_available_meeting_start
    while available_meeting_start < robert_end_time:
        meeting_end = available_meeting_start + meet_duration
        if meeting_end <= robert_end_time and total_meeting_time + meet_duration <= timedelta(minutes=240):
            meeting_times.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Robert",
                "start_time": available_meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            })
            total_meeting_time += meet_duration
            available_meeting_start = meeting_end  # Move start to the end of the last meeting
        else:
            break

    return meeting_times

# Run the schedule calculation
itinerary = calculate_schedule()

# Prepare output in the required JSON format
output = {
    "itinerary": itinerary
}

# Print the JSON formatted output
print(json.dumps(output, indent=2))