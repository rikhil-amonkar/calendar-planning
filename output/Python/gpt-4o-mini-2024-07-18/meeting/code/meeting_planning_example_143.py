import json
from datetime import datetime, timedelta

def format_time(dt):
    return dt.strftime("%H:%M")

def calculate_meeting_schedule():
    # Define travel times in minutes
    travel_times = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
    }

    # Define the meeting constraints
    arrival_time = datetime.strptime("09:00", "%H:%M")
    karen_start = datetime.strptime("18:45", "%H:%M")
    karen_end = datetime.strptime("20:15", "%H:%M")
    mark_start = datetime.strptime("13:00", "%H:%M")
    mark_end = datetime.strptime("17:45", "%H:%M")
    
    # Minimum meeting durations
    karen_meeting_duration = timedelta(minutes=90)
    mark_meeting_duration = timedelta(minutes=120)

    # Calculate meeting times
    itinerary = []

    # Meeting with Mark at Embarcadero
    travel_to_em = travel_times[("North Beach", "Embarcadero")]
    start_mark = max(arrival_time + timedelta(minutes=travel_to_em), mark_start)
    end_mark = start_mark + mark_meeting_duration
    
    if end_mark <= mark_end:
        itinerary.append({
            "action": "meet",
            "location": "Embarcadero",
            "person": "Mark",
            "start_time": format_time(start_mark),
            "end_time": format_time(end_mark),
        })
        
        # Travel to Pacific Heights for Karen
        travel_to_karen = travel_times[("Embarcadero", "Pacific Heights")]
        travel_to_northbeach_return = travel_times[("Embarcadero", "North Beach")]
        
        # Time after the meeting with Mark
        available_time_after_mark = end_mark + timedelta(minutes=travel_to_karen)

        # Check if we can meet Karen after meeting Mark
        if available_time_after_mark <= karen_start:
            # Travel to North Beach to return to Pacific Heights
            travel_to_north_karen = travel_times[("North Beach", "Pacific Heights")]
            arrive_at_karen = karen_start + timedelta(minutes=travel_to_north_karen)
            if arrive_at_karen + karen_meeting_duration <= karen_end:
                itinerary.append({
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Karen",
                    "start_time": format_time(arrive_at_karen),
                    "end_time": format_time(arrive_at_karen + karen_meeting_duration),
                })
    
    return {
        "itinerary": itinerary
    }

schedule = calculate_meeting_schedule()
print(json.dumps(schedule, indent=2))