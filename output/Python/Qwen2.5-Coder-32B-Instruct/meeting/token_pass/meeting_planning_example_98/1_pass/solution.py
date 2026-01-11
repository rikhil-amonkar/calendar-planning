import json
from datetime import datetime, timedelta

# Constants
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_to_richmond = timedelta(minutes=12)
travel_to_alamo = timedelta(minutes=13)
timothy_start = datetime.strptime("20:45", "%H:%M")
timothy_end = datetime.strptime("21:30", "%H:%M")
minimum_meeting_time = timedelta(minutes=45)

def format_time(time):
    return time.strftime("%H:%M")

def compute_schedule():
    itinerary = []
    
    # Start at Alamo Square
    current_time = arrival_time
    
    # Check if we can make it to Richmond District in time for Timothy
    potential_travel_time = timothy_start - travel_to_richmond
    if current_time <= potential_travel_time:
        # Travel to Richmond District
        travel_time = potential_travel_time - current_time
        current_time = potential_travel_time
        
        # Meet Timothy
        meeting_start = current_time
        meeting_end = meeting_start + minimum_meeting_time
        
        # Ensure meeting doesn't exceed Timothy's availability
        if meeting_end <= timothy_end:
            itinerary.append({
                "action": "meet",
                "location": "Richmond District",
                "person": "Timothy",
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
        else:
            # Adjust meeting end time to fit within Timothy's availability
            meeting_end = timothy_end
            itinerary.append({
                "action": "meet",
                "location": "Richmond District",
                "person": "Timothy",
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
    
    return itinerary

schedule = {
    "itinerary": compute_schedule()
}

print(json.dumps(schedule, indent=2))