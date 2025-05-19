import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def compute_schedule():
    # Input parameters
    arrival_time = parse_time("9:00")
    arrival_location = "Nob Hill"
    
    # Friend constraints
    thomas_available_start = parse_time("15:30")
    thomas_available_end = parse_time("19:15")
    thomas_location = "Pacific Heights"
    thomas_min_duration = timedelta(minutes=75)
    
    kenneth_available_start = parse_time("12:00")
    kenneth_available_end = parse_time("15:45")
    kenneth_location = "Mission District"
    kenneth_min_duration = timedelta(minutes=45)
    
    # Travel times in minutes
    travel_times = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16
    }
    
    # Possible schedules
    possible_schedules = []
    
    # Option 1: Meet Kenneth first, then Thomas
    # Travel to Kenneth
    travel_to_kenneth = timedelta(minutes=travel_times[(arrival_location, kenneth_location)])
    meet_kenneth_start = max(arrival_time + travel_to_kenneth, kenneth_available_start)
    meet_kenneth_end = meet_kenneth_start + kenneth_min_duration
    if meet_kenneth_end <= kenneth_available_end:
        # Travel to Thomas
        travel_to_thomas = timedelta(minutes=travel_times[(kenneth_location, thomas_location)])
        meet_thomas_start = max(meet_kenneth_end + travel_to_thomas, thomas_available_start)
        meet_thomas_end = meet_thomas_start + thomas_min_duration
        if meet_thomas_end <= thomas_available_end:
            possible_schedules.append([
                {"action": "meet", "location": kenneth_location, "person": "Kenneth", 
                 "start_time": format_time(meet_kenneth_start), "end_time": format_time(meet_kenneth_end)},
                {"action": "meet", "location": thomas_location, "person": "Thomas", 
                 "start_time": format_time(meet_thomas_start), "end_time": format_time(meet_thomas_end)}
            ])
    
    # Option 2: Meet Thomas first, then Kenneth (if possible)
    # Travel to Thomas
    travel_to_thomas = timedelta(minutes=travel_times[(arrival_location, thomas_location)])
    meet_thomas_start = max(arrival_time + travel_to_thomas, thomas_available_start)
    meet_thomas_end = meet_thomas_start + thomas_min_duration
    if meet_thomas_end <= thomas_available_end:
        # Travel to Kenneth
        travel_to_kenneth = timedelta(minutes=travel_times[(thomas_location, kenneth_location)])
        meet_kenneth_start = max(meet_thomas_end + travel_to_kenneth, kenneth_available_start)
        meet_kenneth_end = meet_kenneth_start + kenneth_min_duration
        if meet_kenneth_end <= kenneth_available_end:
            possible_schedules.append([
                {"action": "meet", "location": thomas_location, "person": "Thomas", 
                 "start_time": format_time(meet_thomas_start), "end_time": format_time(meet_thomas_end)},
                {"action": "meet", "location": kenneth_location, "person": "Kenneth", 
                 "start_time": format_time(meet_kenneth_start), "end_time": format_time(meet_kenneth_end)}
            ])
    
    # Select the best schedule (most meetings, then earliest completion)
    if not possible_schedules:
        return {"itinerary": []}
    
    best_schedule = max(possible_schedules, key=lambda s: (len(s), -parse_time(s[-1]["end_time"]).timestamp()))
    
    return {"itinerary": best_schedule}

if __name__ == "__main__":
    schedule = compute_schedule()
    print(json.dumps(schedule, indent=2))