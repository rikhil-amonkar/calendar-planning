import json
from datetime import datetime, timedelta

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = datetime.strptime("9:00", "%H:%M")
    daniel_available_start = datetime.strptime("19:00", "%H:%M")
    daniel_available_end = datetime.strptime("20:15", "%H:%M")
    min_meeting_duration = timedelta(minutes=75)
    travel_time_to_richmond = timedelta(minutes=14)
    travel_time_back = timedelta(minutes=13)
    
    # Calculate possible meeting window
    meeting_start = daniel_available_start
    meeting_end = meeting_start + min_meeting_duration
    
    if meeting_end > daniel_available_end:
        # Try to adjust by starting earlier
        meeting_end = daniel_available_end
        meeting_start = meeting_end - min_meeting_duration
        if meeting_start < daniel_available_start:
            # Not enough time to meet
            return {"itinerary": []}
    
    # Calculate departure time from Russian Hill
    departure_time = meeting_start - travel_time_to_richmond
    
    # Calculate return time to Russian Hill
    return_time = meeting_end + travel_time_back
    
    # Check if schedule is feasible with arrival time
    if departure_time < arrival_time:
        return {"itinerary": []}
    
    # Format the itinerary
    itinerary = [
        {
            "action": "travel",
            "location": "Richmond District",
            "person": "self",
            "start_time": departure_time.strftime("%H:%M"),
            "end_time": meeting_start.strftime("%H:%M")
        },
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Daniel",
            "start_time": meeting_start.strftime("%H:%M"),
            "end_time": meeting_end.strftime("%H:%M")
        },
        {
            "action": "travel",
            "location": "Russian Hill",
            "person": "self",
            "start_time": meeting_end.strftime("%H:%M"),
            "end_time": return_time.strftime("%H:%M")
        }
    ]
    
    return {"itinerary": itinerary}

# Compute and output the result
result = calculate_optimal_schedule()
print(json.dumps(result, indent=2))