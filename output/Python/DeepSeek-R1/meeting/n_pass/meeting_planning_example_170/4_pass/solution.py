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
        "North Beach": {
            "Union Square": 7,
            "Russian Hill": 4
        },
        "Union Square": {
            "Russian Hill": 13
        }
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
    
    # Free time at North Beach until departure to Emily
    travel_to_emily = travel_times[current_location][emily_location]
    departure_to_emily = emily_start - travel_to_emily
    if current_time < departure_to_emily:
        itinerary.append({
            "action": "free",
            "location": current_location,
            "start_time": minutes_to_time(current_time),
            "end_time": minutes_to_time(departure_to_emily)
        })
    
    # Travel to Emily
    arrival_at_emily = departure_to_emily + travel_to_emily
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": emily_location,
        "start_time": minutes_to_time(departure_to_emily),
        "end_time": minutes_to_time(arrival_at_emily)
    })
    current_location = emily_location
    current_time = arrival_at_emily
    
    # Meet Emily for full available time
    emily_meeting_end = emily_end
    itinerary.append({
        "action": "meet",
        "location": emily_location,
        "person": "Emily",
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(emily_meeting_end)
    })
    current_time = emily_meeting_end
    
    # Travel to Margaret
    travel_to_margaret = travel_times[current_location][margaret_location]
    arrival_at_margaret = current_time + travel_to_margaret
    itinerary.append({
        "action": "travel",
        "from": current_location,
        "to": margaret_location,
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(arrival_at_margaret)
    })
    current_location = margaret_location
    current_time = arrival_at_margaret
    
    # Free time before Margaret's meeting if arrived early
    if current_time < margaret_start:
        itinerary.append({
            "action": "free",
            "location": current_location,
            "start_time": minutes_to_time(current_time),
            "end_time": minutes_to_time(margaret_start)
        })
        current_time = margaret_start
    
    # Meet Margaret for required duration
    margaret_meeting_end = min(margaret_start + margaret_min_duration, margaret_end)
    itinerary.append({
        "action": "meet",
        "location": margaret_location,
        "person": "Margaret",
        "start_time": minutes_to_time(current_time),
        "end_time": minutes_to_time(margaret_meeting_end)
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()