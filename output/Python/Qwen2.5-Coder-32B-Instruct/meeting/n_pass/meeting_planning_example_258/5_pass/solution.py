import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
}

# Define meeting constraints
constraints = {
    "Betty": {"location": "Presidio", "start": "11:32", "end": "12:17", "min_duration": 45},
    "David": {"location": "Richmond District", "start": "13:00", "end": "14:30", "min_duration": 90},
    "Barbara": {"location": "Fisherman's Wharf", "start": "09:15", "end": "11:15", "min_duration": 120},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def add_minutes(time, minutes):
    return (datetime.combine(datetime.today(), time) + timedelta(minutes=minutes)).time()

def can_meet(start, end, min_duration):
    return (datetime.combine(datetime.today(), end) - datetime.combine(datetime.today(), start)).seconds / 60 >= min_duration

def find_optimal_schedule(constraints, travel_times):
    start_time = parse_time("9:00")
    current_location = "Embarcadero"
    itinerary = []

    def visit(location, start, end, person, min_duration):
        nonlocal current_location, start_time, itinerary
        travel_time = travel_times[(current_location, location)]
        arrival_time = add_minutes(start_time, travel_time)
        
        # Adjust arrival time if it's earlier than the meeting start time
        if arrival_time < start:
            arrival_time = start
        
        # Calculate meeting end time
        meeting_end_time = add_minutes(arrival_time, min_duration)
        
        # Check if the meeting can be scheduled within the allowed time frame
        if meeting_end_time <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": arrival_time.strftime("%H:%M"),
                "end_time": meeting_end_time.strftime("%H:%M")
            })
            start_time = meeting_end_time
            current_location = location
        else:
            print(f"Cannot schedule meeting with {person} at {location} from {arrival_time.strftime('%H:%M')} to {meeting_end_time.strftime('%H:%M')}")

    # Sort constraints by earliest available start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: parse_time(x[1]["start"]))

    for person, details in sorted_constraints:
        visit(details["location"], parse_time(details["start"]), parse_time(details["end"]), person, details["min_duration"])

    return itinerary

optimal_itinerary = find_optimal_schedule(constraints, travel_times)
output = {"itinerary": optimal_itinerary}
print(json.dumps(output))