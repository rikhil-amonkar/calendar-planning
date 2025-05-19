import json
from datetime import datetime, timedelta

# Constants for travel distances
TRAVEL_TIME_RH_TO_RD = 14  # minutes
TRAVEL_TIME_RD_TO_RH = 13  # minutes

# Meeting constraints
arrival_time = datetime.strptime("09:00", "%H:%M")
barbara_start_time = datetime.strptime("13:15", "%H:%M")
barbara_end_time = datetime.strptime("18:15", "%H:%M")
minimum_meeting_duration = timedelta(minutes=45)

# Function to calculate the meeting schedule
def compute_meeting_schedule():
    # Calculate possible meeting time window
    meeting_start_time = max(barbara_start_time, arrival_time + timedelta(minutes=TRAVEL_TIME_RH_TO_RD))
    meeting_end_time = barbara_end_time - minimum_meeting_duration
    
    # Check if meeting is possible within the constraints
    if meeting_start_time + minimum_meeting_duration > meeting_end_time:
        return None  # No feasible time for the meeting
    
    # Schedule the meeting
    actual_meeting_start_time = meeting_start_time
    actual_meeting_end_time = actual_meeting_start_time + minimum_meeting_duration
    
    itinerary = [
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Barbara",
            "start_time": actual_meeting_start_time.strftime("%H:%M"),
            "end_time": actual_meeting_end_time.strftime("%H:%M"),
        }
    ]
    
    return {"itinerary": itinerary}

# Compute the schedule
schedule = compute_meeting_schedule()

# Print the output in JSON format
if schedule is not None:
    print(json.dumps(schedule, indent=4))
else:
    print(json.dumps({"itinerary": []}, indent=4))