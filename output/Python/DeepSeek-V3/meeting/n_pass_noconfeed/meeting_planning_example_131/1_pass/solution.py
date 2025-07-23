import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def main():
    # Input parameters
    travel_times = {
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Presidio"): 10,
    }
    
    # Correcting typo in Marina District
    travel_times[("Presidio", "Marina District")] = travel_times.pop(("Presidio", "Marina District"))
    travel_times[("Marina District", "Presidio")] = travel_times.pop(("Marina District", "Presidio"))
    
    start_location = "Pacific Heights"
    start_time = parse_time("9:00")
    
    jason_location = "Presidio"
    jason_window_start = parse_time("10:00")
    jason_window_end = parse_time("16:15")
    jason_duration = 90
    
    kenneth_location = "Marina District"
    kenneth_window_start = parse_time("15:30")
    kenneth_window_end = parse_time("16:45")
    kenneth_duration = 45
    
    # Generate possible schedules
    best_schedule = []
    max_meetings = 0
    
    # Option 1: Meet Jason first, then Kenneth
    # Calculate earliest arrival at Presidio
    travel_to_jason = travel_times[(start_location, jason_location)]
    earliest_jason_start = start_time + timedelta(minutes=travel_to_jason)
    jason_start = max(earliest_jason_start, jason_window_start)
    jason_end = jason_start + timedelta(minutes=jason_duration)
    if jason_end > jason_window_end:
        option1_valid = False
    else:
        # Travel to Kenneth
        travel_to_kenneth = travel_times[(jason_location, kenneth_location)]
        earliest_kenneth_start = jason_end + timedelta(minutes=travel_to_kenneth)
        kenneth_start = max(earliest_kenneth_start, kenneth_window_start)
        kenneth_end = kenneth_start + timedelta(minutes=kenneth_duration)
        if kenneth_end > kenneth_window_end:
            option1_valid = False
        else:
            option1_schedule = [
                {"action": "meet", "location": jason_location, "person": "Jason", 
                 "start_time": format_time(jason_start), "end_time": format_time(jason_end)},
                {"action": "meet", "location": kenneth_location, "person": "Kenneth", 
                 "start_time": format_time(kenneth_start), "end_time": format_time(kenneth_end)}
            ]
            option1_valid = True
    
    # Option 2: Meet Kenneth first, then Jason
    # Calculate earliest arrival at Marina District
    travel_to_kenneth = travel_times[(start_location, kenneth_location)]
    earliest_kenneth_start = start_time + timedelta(minutes=travel_to_kenneth)
    kenneth_start = max(earliest_kenneth_start, kenneth_window_start)
    kenneth_end = kenneth_start + timedelta(minutes=kenneth_duration)
    if kenneth_end > kenneth_window_end:
        option2_valid = False
    else:
        # Travel to Jason
        travel_to_jason = travel_times[(kenneth_location, jason_location)]
        earliest_jason_start = kenneth_end + timedelta(minutes=travel_to_jason)
        jason_start = max(earliest_jason_start, jason_window_start)
        jason_end = jason_start + timedelta(minutes=jason_duration)
        if jason_end > jason_window_end:
            option2_valid = False
        else:
            option2_schedule = [
                {"action": "meet", "location": kenneth_location, "person": "Kenneth", 
                 "start_time": format_time(kenneth_start), "end_time": format_time(kenneth_end)},
                {"action": "meet", "location": jason_location, "person": "Jason", 
                 "start_time": format_time(jason_start), "end_time": format_time(jason_end)}
            ]
            option2_valid = True
    
    # Option 3: Meet only Jason
    travel_to_jason = travel_times[(start_location, jason_location)]
    earliest_jason_start = start_time + timedelta(minutes=travel_to_jason)
    jason_start = max(earliest_jason_start, jason_window_start)
    jason_end = jason_start + timedelta(minutes=jason_duration)
    if jason_end <= jason_window_end:
        option3_schedule = [
            {"action": "meet", "location": jason_location, "person": "Jason", 
             "start_time": format_time(jason_start), "end_time": format_time(jason_end)}
        ]
        option3_valid = True
    else:
        option3_valid = False
    
    # Option 4: Meet only Kenneth
    travel_to_kenneth = travel_times[(start_location, kenneth_location)]
    earliest_kenneth_start = start_time + timedelta(minutes=travel_to_kenneth)
    kenneth_start = max(earliest_kenneth_start, kenneth_window_start)
    kenneth_end = kenneth_start + timedelta(minutes=kenneth_duration)
    if kenneth_end <= kenneth_window_end:
        option4_schedule = [
            {"action": "meet", "location": kenneth_location, "person": "Kenneth", 
             "start_time": format_time(kenneth_start), "end_time": format_time(kenneth_end)}
        ]
        option4_valid = True
    else:
        option4_valid = False
    
    # Determine best option
    best_schedule = []
    if option1_valid:
        best_schedule = option1_schedule
    if option2_valid and len(option2_schedule) > len(best_schedule):
        best_schedule = option2_schedule
    if option3_valid and len(option3_schedule) > len(best_schedule):
        best_schedule = option3_schedule
    if option4_valid and len(option4_schedule) > len(best_schedule):
        best_schedule = option4_schedule
    
    # Prepare output
    output = {
        "itinerary": best_schedule
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()