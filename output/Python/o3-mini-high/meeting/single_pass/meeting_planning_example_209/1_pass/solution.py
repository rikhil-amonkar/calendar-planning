#!/usr/bin/env python3
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times in minutes between locations
    travel_times = {
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 29,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "North Beach"): 5,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Russian Hill"): 4,
    }
    
    # Define meeting constraints for each friend.
    # Times are represented as minutes since midnight.
    constraints = {
        "Anthony": {
            "location": "Chinatown",
            "available_start": 13 * 60 + 15,  # 13:15
            "available_end": 14 * 60 + 30,      # 14:30
            "min_duration": 60
        },
        "Rebecca": {
            "location": "Russian Hill",
            "available_start": 19 * 60 + 30,    # 19:30
            "available_end": 21 * 60 + 15,        # 21:15
            "min_duration": 105
        },
        "Melissa": {
            "location": "North Beach",
            "available_start": 8 * 60 + 15,     # 8:15
            "available_end": 13 * 60 + 30,        # 13:30
            "min_duration": 105
        }
    }
    
    # Starting point and time: Sunset District at 9:00 AM
    start_location = "Sunset District"
    current_time = 9 * 60  # 9:00 AM in minutes

    itinerary = []
    
    # Plan to meet Melissa first at North Beach.
    # Travel from Sunset District to North Beach.
    travel = travel_times[(start_location, constraints["Melissa"]["location"])]
    arrival_time = current_time + travel  # Arrival time at North Beach.
    # Meeting with Melissa can start when both you have arrived and she is available.
    melissa_start = max(arrival_time, constraints["Melissa"]["available_start"])
    melissa_end = melissa_start + constraints["Melissa"]["min_duration"]
    if melissa_end > constraints["Melissa"]["available_end"]:
        raise Exception("Cannot schedule meeting with Melissa within her available time.")
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Melissa"]["location"],
        "person": "Melissa",
        "start_time": minutes_to_time_str(melissa_start),
        "end_time": minutes_to_time_str(melissa_end)
    })
    
    # Next, plan to meet Anthony at Chinatown.
    # Travel from North Beach to Chinatown.
    travel = travel_times[(constraints["Melissa"]["location"], constraints["Anthony"]["location"])]
    arrival_time = melissa_end + travel
    anthony_start = max(arrival_time, constraints["Anthony"]["available_start"])
    anthony_end = anthony_start + constraints["Anthony"]["min_duration"]
    if anthony_end > constraints["Anthony"]["available_end"]:
        raise Exception("Cannot schedule meeting with Anthony within his available time.")
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Anthony"]["location"],
        "person": "Anthony",
        "start_time": minutes_to_time_str(anthony_start),
        "end_time": minutes_to_time_str(anthony_end)
    })
    
    # Finally, plan to meet Rebecca at Russian Hill.
    # Travel from Chinatown to Russian Hill.
    travel = travel_times[(constraints["Anthony"]["location"], constraints["Rebecca"]["location"])]
    arrival_time = anthony_end + travel
    rebecca_start = max(arrival_time, constraints["Rebecca"]["available_start"])
    rebecca_end = rebecca_start + constraints["Rebecca"]["min_duration"]
    if rebecca_end > constraints["Rebecca"]["available_end"]:
        raise Exception("Cannot schedule meeting with Rebecca within her available time.")
        
    itinerary.append({
        "action": "meet",
        "location": constraints["Rebecca"]["location"],
        "person": "Rebecca",
        "start_time": minutes_to_time_str(rebecca_start),
        "end_time": minutes_to_time_str(rebecca_end)
    })
    
    # Output the itinerary as a JSON-formatted dictionary.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()