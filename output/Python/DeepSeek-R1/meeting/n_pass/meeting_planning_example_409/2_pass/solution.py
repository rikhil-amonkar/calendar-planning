import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    travel_times = {
        "Fisherman's Wharf": {"Bayview": 26, "Golden Gate Park": 25, "Nob Hill": 11, "Marina District": 9, "Embarcadero": 8},
        "Bayview": {"Fisherman's Wharf": 25, "Golden Gate Park": 22, "Nob Hill": 20, "Marina District": 25, "Embarcadero": 19},
        "Golden Gate Park": {"Fisherman's Wharf": 24, "Bayview": 23, "Nob Hill": 20, "Marina District": 16, "Embarcadero": 25},
        "Nob Hill": {"Fisherman's Wharf": 11, "Bayview": 19, "Golden Gate Park": 17, "Marina District": 11, "Embarcadero": 9},
        "Marina District": {"Fisherman's Wharf": 10, "Bayview": 27, "Golden Gate Park": 18, "Nob Hill": 12, "Embarcadero": 14},
        "Embarcadero": {"Fisherman's Wharf": 6, "Bayview": 21, "Golden Gate Park": 25, "Nob Hill": 10, "Marina District": 12}
    }

    friends = [
        {"name": "Laura", "location": "Nob Hill", "start": "8:45", "end": "16:15", "min": 30},
        {"name": "Thomas", "location": "Bayview", "start": "15:30", "end": "18:30", "min": 120},
        {"name": "Patricia", "location": "Embarcadero", "start": "17:30", "end": "22:00", "min": 45},
        {"name": "Betty", "location": "Marina District", "start": "18:45", "end": "21:45", "min": 45},
        {"name": "Stephanie", "location": "Golden Gate Park", "start": "18:30", "end": "21:45", "min": 30}
    ]

    for friend in friends:
        friend['start_min'] = time_to_minutes(friend['start'])
        friend['end_min'] = time_to_minutes(friend['end'])
    
    # Sort friends by the start of their availability window
    friends_sorted = sorted(friends, key=lambda x: x['start_min'])

    current_location = "Fisherman's Wharf"
    current_time = time_to_minutes("9:00")
    itinerary = []

    for friend in friends_sorted:
        from_loc = current_location
        to_loc = friend['location']
        travel_time = travel_times[from_loc][to_loc]
        
        # Calculate departure time to arrive at friend's location by their start time
        departure_time = max(current_time, friend['start_min'] - travel_time)
        arrival_time = departure_time + travel_time
        meeting_start = max(arrival_time, friend['start_min'])
        meeting_end = meeting_start + friend['min']
        
        # Check if meeting can be scheduled within friend's availability
        if meeting_end <= friend['end_min']:
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']

    # Add return to Fisherman's Wharf after last meeting
    return_time = travel_times[current_location]["Fisherman's Wharf"]
    return_start = current_time
    return_arrival = return_start + return_time
    # This return trip isn't added to itinerary as per requirements

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()