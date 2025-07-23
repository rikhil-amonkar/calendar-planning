import json
from datetime import datetime, timedelta

def calculate_schedule():
    # Input parameters
    arrival_time = datetime.strptime("9:00", "%H:%M")
    joshua_start = datetime.strptime("20:45", "%H:%M")
    joshua_end = datetime.strptime("21:45", "%H:%M")
    min_meet_duration = timedelta(minutes=15)
    sunset_to_golden_gate = timedelta(minutes=11)
    golden_gate_to_sunset = timedelta(minutes=10)
    
    # Calculate possible meeting window with Joshua
    travel_to_joshua = sunset_to_golden_gate
    travel_back = golden_gate_to_sunset
    
    # Earliest we can arrive at Golden Gate Park
    earliest_arrival = arrival_time + travel_to_joshua
    
    # Latest we can leave Golden Gate Park to meet Joshua for 15 minutes
    latest_departure = joshua_end - min_meet_duration
    
    # The actual meeting window is the intersection of Joshua's availability and our travel constraints
    meeting_start = max(earliest_arrival, joshua_start)
    meeting_end = min(meeting_start + min_meet_duration, joshua_end)
    
    # Check if meeting is possible
    if meeting_start >= joshua_start and meeting_end <= joshua_end and (meeting_end - meeting_start) >= min_meet_duration:
        itinerary = [
            {
                "action": "travel",
                "location": "Golden Gate Park",
                "person": None,
                "start_time": arrival_time.strftime("%H:%M"),
                "end_time": earliest_arrival.strftime("%H:%M")
            },
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Joshua",
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            },
            {
                "action": "travel",
                "location": "Sunset District",
                "person": None,
                "start_time": meeting_end.strftime("%H:%M"),
                "end_time": (meeting_end + travel_back).strftime("%H:%M")
            }
        ]
    else:
        itinerary = [
            {
                "action": "no_meeting_possible",
                "location": None,
                "person": None,
                "start_time": None,
                "end_time": None
            }
        ]
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))