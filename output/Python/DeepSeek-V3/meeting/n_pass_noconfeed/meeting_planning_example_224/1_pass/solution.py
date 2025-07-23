import json

def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Travel times in minutes
    travel_times = {
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Richmond District'): 7,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Presidio'): 7
    }

    # Constraints
    start_location = "Fisherman's Wharf"
    current_time = parse_time("9:00")
    current_location = start_location

    melissa_available_start = parse_time("8:30")
    melissa_available_end = parse_time("20:00")
    melissa_min_duration = 15
    melissa_location = "Golden Gate Park"

    nancy_available_start = parse_time("19:45")
    nancy_available_end = parse_time("22:00")
    nancy_min_duration = 105
    nancy_location = "Presidio"

    emily_available_start = parse_time("16:45")
    emily_available_end = parse_time("22:00")
    emily_min_duration = 120
    emily_location = "Richmond District"

    itinerary = []

    # Try to meet Melissa first
    travel_time = travel_times[(current_location, melissa_location)]
    arrival_time = current_time + travel_time
    if arrival_time <= melissa_available_end - melissa_min_duration:
        meet_start = max(arrival_time, melissa_available_start)
        meet_end = meet_start + melissa_min_duration
        itinerary.append({
            "action": "meet",
            "location": melissa_location,
            "person": "Melissa",
            "start_time": format_time(meet_start),
            "end_time": format_time(meet_end)
        })
        current_time = meet_end
        current_location = melissa_location

    # Try to meet Emily next
    travel_time = travel_times[(current_location, emily_location)]
    arrival_time = current_time + travel_time
    if arrival_time <= emily_available_end - emily_min_duration:
        meet_start = max(arrival_time, emily_available_start)
        meet_end = meet_start + emily_min_duration
        itinerary.append({
            "action": "meet",
            "location": emily_location,
            "person": "Emily",
            "start_time": format_time(meet_start),
            "end_time": format_time(meet_end)
        })
        current_time = meet_end
        current_location = emily_location

    # Try to meet Nancy last
    travel_time = travel_times[(current_location, nancy_location)]
    arrival_time = current_time + travel_time
    if arrival_time <= nancy_available_end - nancy_min_duration:
        meet_start = max(arrival_time, nancy_available_start)
        meet_end = meet_start + nancy_min_duration
        itinerary.append({
            "action": "meet",
            "location": nancy_location,
            "person": "Nancy",
            "start_time": format_time(meet_start),
            "end_time": format_time(meet_end)
        })

    return {"itinerary": itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))