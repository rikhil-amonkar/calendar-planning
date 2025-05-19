import json
from datetime import datetime, timedelta

def calculate_schedule():
    # Input parameters
    arrival_time = datetime.strptime("9:00", "%H:%M")
    daniel_available_start = datetime.strptime("19:00", "%H:%M")
    daniel_available_end = datetime.strptime("20:15", "%H:%M")
    required_meeting_duration = timedelta(minutes=75)
    travel_to_richmond = timedelta(minutes=14)
    travel_to_russian = timedelta(minutes=13)

    # Calculate possible meeting window
    latest_departure_from_russian = daniel_available_end - required_meeting_duration - travel_to_richmond
    earliest_arrival_at_richmond = daniel_available_start + travel_to_richmond

    # Check if meeting is possible
    if latest_departure_from_russian < arrival_time or earliest_arrival_at_richmond > daniel_available_end:
        return {"itinerary": []}

    # Determine optimal meeting time (maximize duration)
    meeting_start = max(daniel_available_start, arrival_time + travel_to_richmond)
    meeting_end = min(daniel_available_end, meeting_start + required_meeting_duration)
    
    if meeting_end > daniel_available_end:
        meeting_end = daniel_available_end
        meeting_start = meeting_end - required_meeting_duration

    # Build itinerary
    itinerary = []
    
    # Add travel to Richmond if needed
    if arrival_time + travel_to_richmond < meeting_start:
        itinerary.append({
            "action": "travel",
            "location": "Richmond District",
            "person": None,
            "start_time": arrival_time.strftime("%-H:%M"),
            "end_time": (arrival_time + travel_to_richmond).strftime("%-H:%M")
        })
    
    # Add meeting with Daniel
    itinerary.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Daniel",
        "start_time": meeting_start.strftime("%-H:%M"),
        "end_time": meeting_end.strftime("%-H:%M")
    })

    # Add return travel if needed
    if meeting_end < datetime.strptime("23:59", "%H:%M"):
        itinerary.append({
            "action": "travel",
            "location": "Russian Hill",
            "person": None,
            "start_time": meeting_end.strftime("%-H:%M"),
            "end_time": (meeting_end + travel_to_russian).strftime("%-H:%M")
        })

    return {"itinerary": itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))