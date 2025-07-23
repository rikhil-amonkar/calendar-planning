import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "Sunset District": {
            "Russian Hill": 24,
            "Chinatown": 30,
            "Presidio": 16,
            "Fisherman's Wharf": 29
        },
        "Russian Hill": {
            "Sunset District": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Fisherman's Wharf": 7
        },
        "Chinatown": {
            "Sunset District": 29,
            "Russian Hill": 7,
            "Presidio": 19,
            "Fisherman's Wharf": 8
        },
        "Presidio": {
            "Sunset District": 15,
            "Russian Hill": 14,
            "Chinatown": 21,
            "Fisherman's Wharf": 19
        },
        "Fisherman's Wharf": {
            "Sunset District": 27,
            "Russian Hill": 7,
            "Chinatown": 12,
            "Presidio": 17
        }
    }
    
    friends = [
        {
            "name": "Robert",
            "location": "Fisherman's Wharf",
            "available_start": time_to_minutes("9:00"),
            "available_end": time_to_minutes("13:45"),
            "min_duration": 30
        },
        {
            "name": "Michelle",
            "location": "Chinatown",
            "available_start": time_to_minutes("8:15"),
            "available_end": time_to_minutes("14:00"),
            "min_duration": 15
        },
        {
            "name": "George",
            "location": "Presidio",
            "available_start": time_to_minutes("10:30"),
            "available_end": time_to_minutes("18:45"),
            "min_duration": 30
        },
        {
            "name": "William",
            "location": "Russian Hill",
            "available_start": time_to_minutes("18:30"),
            "available_end": time_to_minutes("20:45"),
            "min_duration": 105
        }
    ]
    
    current_location = "Sunset District"
    current_time = time_to_minutes("9:00")
    itinerary = []
    
    for friend in friends:
        travel_duration = travel_times[current_location][friend["location"]]
        
        if friend["name"] == "George":
            leave_time = friend["available_end"] - friend["min_duration"] - travel_duration
            current_time = max(current_time, leave_time)
        
        current_time += travel_duration
        
        if friend["name"] == "William":
            desired_start = time_to_minutes("19:00")
            candidate_start = max(current_time, friend["available_start"], desired_start)
            if candidate_start <= friend["available_end"] - friend["min_duration"]:
                start_time = candidate_start
            else:
                start_time = max(current_time, friend["available_start"])
            end_time = start_time + friend["min_duration"]
        else:
            start_time = max(current_time, friend["available_start"])
            end_time = start_time + friend["min_duration"]
        
        if end_time > friend["available_end"]:
            continue
        
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = friend["location"]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()