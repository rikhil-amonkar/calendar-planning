import json

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Travel times in minutes
    travel_times = {
        'Fisherman\'s Wharf': {
            'Golden Gate Park': 25,
            'Presidio': 17,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Fisherman\'s Wharf': 24,
            'Presidio': 11,
            'Richmond District': 7
        },
        'Presidio': {
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 12,
            'Richmond District': 7
        },
        'Richmond District': {
            'Fisherman\'s Wharf': 18,
            'Golden Gate Park': 9,
            'Presidio': 7
        }
    }

    # Constraints
    current_location = 'Fisherman\'s Wharf'
    current_time = time_to_minutes('9:00')

    melissa_available_start = time_to_minutes('8:30')
    melissa_available_end = time_to_minutes('20:00')
    melissa_min_duration = 15
    melissa_location = 'Golden Gate Park'

    nancy_available_start = time_to_minutes('19:45')
    nancy_available_end = time_to_minutes('22:00')
    nancy_min_duration = 105
    nancy_location = 'Presidio'

    emily_available_start = time_to_minutes('16:45')
    emily_available_end = time_to_minutes('22:00')
    emily_min_duration = 120
    emily_location = 'Richmond District'

    itinerary = []

    # Meet Melissa first
    travel_time = travel_times[current_location][melissa_location]
    arrival_time = current_time + travel_time
    if arrival_time <= melissa_available_end:
        meet_start = max(arrival_time, melissa_available_start)
        meet_end = meet_start + melissa_min_duration
        if meet_end <= melissa_available_end:
            itinerary.append({
                "action": "meet",
                "location": melissa_location,
                "person": "Melissa",
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = melissa_location

    # Then meet Emily
    travel_time = travel_times[current_location][emily_location]
    arrival_time = current_time + travel_time
    if arrival_time <= emily_available_end:
        meet_start = max(arrival_time, emily_available_start)
        meet_end = meet_start + emily_min_duration
        if meet_end <= emily_available_end:
            itinerary.append({
                "action": "meet",
                "location": emily_location,
                "person": "Emily",
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            })
            current_time = meet_end
            current_location = emily_location

    # Finally meet Nancy
    travel_time = travel_times[current_location][nancy_location]
    arrival_time = current_time + travel_time
    if arrival_time <= nancy_available_end:
        meet_start = max(arrival_time, nancy_available_start)
        meet_end = meet_start + nancy_min_duration
        if meet_end <= nancy_available_end:
            itinerary.append({
                "action": "meet",
                "location": nancy_location,
                "person": "Nancy",
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))