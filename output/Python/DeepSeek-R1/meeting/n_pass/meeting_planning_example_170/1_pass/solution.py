import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    travel_times = {
        "North Beach": {"Union Square": 7, "Russian Hill": 4},
        "Union Square": {"North Beach": 10, "Russian Hill": 13},
        "Russian Hill": {"North Beach": 5, "Union Square": 11}
    }
    
    current_location = "North Beach"
    current_time = time_to_minutes("9:00")
    
    emily_location = "Union Square"
    emily_start = time_to_minutes("16:00")
    emily_end = time_to_minutes("17:15")
    emily_min_duration = 45
    
    margaret_location = "Russian Hill"
    margaret_start = time_to_minutes("19:00")
    margaret_end = time_to_minutes("21:00")
    margaret_min_duration = 120
    
    itinerary = []
    
    # Travel to Emily
    travel_to_emily = travel_times[current_location][emily_location]
    emily_arrival = emily_start
    departure_time = emily_arrival - travel_to_emily
    emily_departure = min(emily_end, margaret_start - travel_times[emily_location][margaret_location])
    emily_meeting_duration = emily_departure - emily_arrival
    
    if emily_meeting_duration >= emily_min_duration:
        itinerary.append({
            "action": "meet",
            "location": emily_location,
            "person": "Emily",
            "start_time": minutes_to_time(emily_arrival),
            "end_time": minutes_to_time(emily_departure)
        })
        current_location = emily_location
        current_time = emily_departure
    
    # Travel to Margaret
    travel_to_margaret = travel_times[current_location][margaret_location]
    margaret_arrival = current_time + travel_to_margaret
    margaret_meeting_start = max(margaret_arrival, margaret_start)
    margaret_meeting_end = min(margaret_meeting_start + margaret_min_duration, margaret_end)
    
    if margaret_meeting_end - margaret_meeting_start >= margaret_min_duration:
        itinerary.append({
            "action": "meet",
            "location": margaret_location,
            "person": "Margaret",
            "start_time": minutes_to_time(margaret_meeting_start),
            "end_time": minutes_to_time(margaret_meeting_end)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()