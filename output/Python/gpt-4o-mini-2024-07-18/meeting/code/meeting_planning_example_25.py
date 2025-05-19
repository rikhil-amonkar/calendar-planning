import json
from datetime import datetime, timedelta

# Constants
TRAVEL_TIME = 23  # minutes to travel between Golden Gate Park and Chinatown
ARRIVAL_TIME = datetime.strptime("9:00", "%H:%M")
DAVID_START_TIME = datetime.strptime("16:00", "%H:%M")
DAVID_END_TIME = datetime.strptime("21:45", "%H:%M")
MIN_MEETING_TIME = timedelta(minutes=105)

def calculate_schedule():
    # Start at Golden Gate Park
    current_time = ARRIVAL_TIME
    itinerary = []

    # Possible evening schedule with David
    # 1. Leave Golden Gate Park at the latest 15:37 to meet David for 105 minutes
    latest_david_meet_start = DAVID_START_TIME - MIN_MEETING_TIME

    # 2. If we can meet David while arriving no later than 15:37
    while current_time < latest_david_meet_start:
        # Meet a friend at Golden Gate Park for 1 hour
        meeting_start = current_time
        meeting_end = current_time + timedelta(hours=1)  # 1 hour meeting
        
        # Add the meeting to the itinerary
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Friend",
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M")
        })
        
        # Move current time forward
        current_time = meeting_end

    # 3. Now travel to Chinatown to meet David
    if current_time + timedelta(minutes=TRAVEL_TIME) <= DAVID_END_TIME:
        travel_time = current_time + timedelta(minutes=TRAVEL_TIME)
        
        # Meet David from the latest possible start
        david_meeting_start = travel_time
        david_meeting_end = david_meeting_start + MIN_MEETING_TIME
        
        # Add David meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "David",
            "start_time": david_meeting_start.strftime("%H:%M"),
            "end_time": david_meeting_end.strftime("%H:%M")
        })
        
        # Update current time after meeting with David
        current_time = david_meeting_end

    return {"itinerary": itinerary}

# Calculate the schedule
schedule = calculate_schedule()

# Output as JSON
print(json.dumps(schedule, indent=2))