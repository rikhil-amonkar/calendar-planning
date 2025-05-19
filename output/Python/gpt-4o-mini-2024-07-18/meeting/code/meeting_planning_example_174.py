import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Mission District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Pacific Heights"): 16,
}

# Meeting constraints
arrival_time = datetime.strptime("09:00", "%H:%M")
thomas_availability_start = datetime.strptime("15:30", "%H:%M")
thomas_availability_end = datetime.strptime("19:15", "%H:%M")
min_thomas_meeting_duration = timedelta(minutes=75)

kenneth_availability_start = datetime.strptime("12:00", "%H:%M")
kenneth_availability_end = datetime.strptime("15:45", "%H:%M")
min_kenneth_meeting_duration = timedelta(minutes=45)

# Function to calculate time after traveling
def travel_time(start_location, end_location):
    return travel_times.get((start_location, end_location), travel_times.get((end_location, start_location), float('inf')))

# Function to create a meeting schedule
def create_schedule():
    schedule = []
    
    # Meet Kenneth
    # Travel from Nob Hill to Mission District
    travel_to_kenneth = travel_time("Nob Hill", "Mission District")
    start_meeting_kenneth = kenneth_availability_start - timedelta(minutes=travel_to_kenneth)
    end_meeting_kenneth = start_meeting_kenneth + min_kenneth_meeting_duration
    
    if end_meeting_kenneth <= kenneth_availability_end:
        # Schedule the meeting with Kenneth
        schedule.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Kenneth",
            "start_time": start_meeting_kenneth.strftime("%H:%M"),
            "end_time": end_meeting_kenneth.strftime("%H:%M"),
        })

        # Travel back to Nob Hill
        travel_back = travel_time("Mission District", "Nob Hill")
        
        # Calculate time after meeting with Kenneth
        time_after_kenneth = end_meeting_kenneth + timedelta(minutes=travel_back)

        # Meet Thomas
        # Travel from Nob Hill to Pacific Heights
        travel_to_thomas = travel_time("Nob Hill", "Pacific Heights")
        start_meeting_thomas = max(time_after_kenneth + timedelta(minutes=travel_to_thomas), thomas_availability_start)
        
        if start_meeting_thomas + min_thomas_meeting_duration <= thomas_availability_end:
            end_meeting_thomas = start_meeting_thomas + min_thomas_meeting_duration
            # Schedule the meeting with Thomas
            schedule.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Thomas",
                "start_time": start_meeting_thomas.strftime("%H:%M"),
                "end_time": end_meeting_thomas.strftime("%H:%M"),
            })
    
    return {
        "itinerary": schedule
    }

# Main logic to create schedule and output JSON
itinerary = create_schedule()
print(json.dumps(itinerary, indent=2))