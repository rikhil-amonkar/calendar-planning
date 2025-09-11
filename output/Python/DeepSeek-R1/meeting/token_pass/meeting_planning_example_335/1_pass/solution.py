import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Mission District"): 15,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Mission District"): 18,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Mission District"): 17,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Financial District"): 17,
        ("Mission District", "Alamo Square"): 11
    }
    
    friends = {
        "Helen": {
            "location": "North Beach",
            "available_start": time_to_minutes("9:00"),
            "available_end": time_to_minutes("17:00"),
            "duration": 15
        },
        "Kevin": {
            "location": "Mission District",
            "available_start": time_to_minutes("10:45"),
            "available_end": time_to_minutes("14:45"),
            "duration": 45
        },
        "Betty": {
            "location": "Financial District",
            "available_start": time_to_minutes("19:00"),
            "available_end": time_to_minutes("21:45"),
            "duration": 90
        },
        "Amanda": {
            "location": "Alamo Square",
            "available_start": time_to_minutes("19:45"),
            "available_end": time_to_minutes("21:00"),
            "duration": 60
        }
    }
    
    day_friends = ["Helen", "Kevin"]
    evening_friends = ["Betty", "Amanda"]
    best_schedule = []
    max_meetings = 0
    
    for day_order in permutations(day_friends):
        current_time = time_to_minutes("9:00")
        current_location = "Pacific Heights"
        meetings = []
        valid = True
        
        for friend_name in day_order:
            friend = friends[friend_name]
            travel_time = travel_times.get((current_location, friend["location"]), float('inf'))
            arrival_time = current_time + travel_time
            start_time = max(arrival_time, friend["available_start"])
            end_time = start_time + friend["duration"]
            
            if end_time > friend["available_end"]:
                valid = False
                break
                
            meetings.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend_name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
            
            current_time = end_time
            current_location = friend["location"]
        
        if not valid:
            continue
            
        for eve_friend_name in evening_friends:
            eve_friend = friends[eve_friend_name]
            travel_time = travel_times.get((current_location, eve_friend["location"]), float('inf'))
            arrival_time = current_time + travel_time
            start_time = max(arrival_time, eve_friend["available_start"])
            end_time = start_time + eve_friend["duration"]
            
            if end_time <= eve_friend["available_end"]:
                eve_meeting = {
                    "action": "meet",
                    "location": eve_friend["location"],
                    "person": eve_friend_name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                }
                total_meetings = meetings + [eve_meeting]
                if len(total_meetings) > max_meetings:
                    max_meetings = len(total_meetings)
                    best_schedule = total_meetings
                break
    
    if not best_schedule:
        best_schedule = meetings
    
    output = {"itinerary": best_schedule}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()