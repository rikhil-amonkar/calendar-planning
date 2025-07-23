import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Travel times dictionary: {from: {to: minutes}}
    travel_times = {
        "Bayview": {
            "Embarcadero": 19,
            "Fisherman's Wharf": 25,
            "Financial District": 19
        },
        "Embarcadero": {
            "Bayview": 21,
            "Fisherman's Wharf": 6,
            "Financial District": 5
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "Embarcadero": 8,
            "Financial District": 11
        },
        "Financial District": {
            "Bayview": 19,
            "Embarcadero": 4,
            "Fisherman's Wharf": 10
        }
    }

    # Constraints
    current_location = "Bayview"
    current_time = parse_time("9:00")
    
    betty_available_start = parse_time("19:45")
    betty_available_end = parse_time("21:45")
    betty_min_duration = timedelta(minutes=15)
    
    karen_available_start = parse_time("8:45")
    karen_available_end = parse_time("15:00")
    karen_min_duration = timedelta(minutes=30)
    
    anthony_available_start = parse_time("9:15")
    anthony_available_end = parse_time("21:30")
    anthony_min_duration = timedelta(minutes=105)
    
    itinerary = []
    
    # Try to meet Karen first (she's only available until 3:00PM)
    travel_to_karen = timedelta(minutes=travel_times[current_location]["Fisherman's Wharf"])
    arrival_karen = current_time + travel_to_karen
    
    if arrival_karen <= karen_available_end - karen_min_duration:
        meet_karen_start = max(arrival_karen, karen_available_start)
        meet_karen_end = meet_karen_start + karen_min_duration
        if meet_karen_end <= karen_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Karen",
                "start_time": format_time(meet_karen_start),
                "end_time": format_time(meet_karen_end)
            })
            current_location = "Fisherman's Wharf"
            current_time = meet_karen_end
    
    # Now try to meet Anthony (longest duration)
    travel_to_anthony = timedelta(minutes=travel_times[current_location]["Financial District"])
    arrival_anthony = current_time + travel_to_anthony
    
    if arrival_anthony <= anthony_available_end - anthony_min_duration:
        meet_anthony_start = max(arrival_anthony, anthony_available_start)
        meet_anthony_end = meet_anthony_start + anthony_min_duration
        if meet_anthony_end <= anthony_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": format_time(meet_anthony_start),
                "end_time": format_time(meet_anthony_end)
            })
            current_location = "Financial District"
            current_time = meet_anthony_end
    
    # Finally try to meet Betty (evening)
    travel_to_betty = timedelta(minutes=travel_times[current_location]["Embarcadero"])
    arrival_betty = current_time + travel_to_betty
    
    if arrival_betty <= betty_available_end - betty_min_duration:
        meet_betty_start = max(arrival_betty, betty_available_start)
        meet_betty_end = meet_betty_start + betty_min_duration
        if meet_betty_end <= betty_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Betty",
                "start_time": format_time(meet_betty_start),
                "end_time": format_time(meet_betty_end)
            })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))