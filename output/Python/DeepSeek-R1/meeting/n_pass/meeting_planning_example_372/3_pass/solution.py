import json
from itertools import permutations

def main():
    # Travel times in minutes
    travel_times = {
        "Sunset District": {
            "Alamo Square": 17,
            "Russian Hill": 24,
            "Golden Gate Park": 11,
            "Mission District": 24
        },
        "Alamo Square": {
            "Sunset District": 16,
            "Russian Hill": 13,
            "Golden Gate Park": 9,
            "Mission District": 10
        },
        "Russian Hill": {
            "Sunset District": 23,
            "Alamo Square": 15,
            "Golden Gate Park": 21,
            "Mission District": 16
        },
        "Golden Gate Park": {
            "Sunset District": 10,
            "Alamo Square": 10,
            "Russian Hill": 19,
            "Mission District": 17
        },
        "Mission District": {
            "Sunset District": 24,
            "Alamo Square": 11,
            "Russian Hill": 15,
            "Golden Gate Park": 17
        }
    }
    
    # Define friends with their constraints (times in minutes since midnight)
    daniel = {
        "name": "Daniel",
        "location": "Golden Gate Park",
        "available_start": 8 * 60,      # 8:00
        "available_end": 13 * 60 + 30,  # 13:30
        "min_duration": 15
    }
    
    margaret = {
        "name": "Margaret",
        "location": "Russian Hill",
        "available_start": 9 * 60,    # 9:00
        "available_end": 16 * 60,      # 16:00
        "min_duration": 30
    }
    
    charles = {
        "name": "Charles",
        "location": "Alamo Square",
        "available_start": 18 * 60,     # 18:00
        "available_end": 20 * 60 + 45,  # 20:45
        "min_duration": 90
    }
    
    stephanie = {
        "name": "Stephanie",
        "location": "Mission District",
        "available_start": 20 * 60 + 30,  # 20:30
        "available_end": 22 * 60,          # 22:00
        "min_duration": 90
    }
    
    friends = [daniel, margaret]
    start_location = "Sunset District"
    start_time = 9 * 60  # 9:00 in minutes
    
    # Evaluate permutations for morning meetings
    candidates = []
    for perm in permutations(friends):
        current_location = start_location
        current_time = start_time
        schedule_morning = []  # store morning meetings
        travel_time_total = 0
        valid = True
        
        for friend in perm:
            # Get travel time to friend's location
            tt = travel_times[current_location][friend["location"]]
            travel_time_total += tt
            current_time += tt  # arrival time at friend's location
            
            # Calculate meeting start time (max of arrival and friend's available start)
            meeting_start = max(current_time, friend["available_start"])
            # Check if meeting can be scheduled within friend's window
            if meeting_start + friend["min_duration"] > friend["available_end"]:
                valid = False
                break
                
            meeting_end = meeting_start + friend["min_duration"]
            schedule_morning.append({
                "friend": friend,
                "start": meeting_start,
                "end": meeting_end
            })
            
            current_time = meeting_end
            current_location = friend["location"]
        
        if not valid:
            continue
        
        # Travel from last morning location to Charles (Alamo Square)
        tt_to_charles = travel_times[current_location]["Alamo Square"]
        travel_time_total += tt_to_charles
        arrival_charles = current_time + tt_to_charles
        
        # Must arrive at Charles by 18:50 to ensure enough time for his meeting + travel to Stephanie
        if arrival_charles > 18*60 + 50:  # 18:50
            continue
        
        # This candidate is valid
        candidates.append({
            "travel_time": travel_time_total,
            "schedule": schedule_morning,
            "arrival_charles": arrival_charles
        })
    
    if not candidates:
        # Fallback: no valid schedule found (shouldn't happen with given constraints)
        best_candidate = None
        itinerary = []
    else:
        best_candidate = min(candidates, key=lambda x: x["travel_time"])
        
        # Build itinerary
        itinerary = []
        
        # Add morning meetings from best_candidate
        for meeting in best_candidate["schedule"]:
            friend = meeting["friend"]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting["start"]),
                "end_time": minutes_to_time_str(meeting["end"])
            })
        
        # Add Charles meeting
        charles_start = max(best_candidate["arrival_charles"], charles["available_start"])
        charles_end = charles_start + charles["min_duration"]
        itinerary.append({
            "action": "meet",
            "location": charles["location"],
            "person": charles["name"],
            "start_time": minutes_to_time_str(charles_start),
            "end_time": minutes_to_time_str(charles_end)
        })
        
        # Add Stephanie meeting (fixed at 20:30-22:00)
        stephanie_start = stephanie["available_start"]
        stephanie_end = stephanie_start + stephanie["min_duration"]
        itinerary.append({
            "action": "meet",
            "location": stephanie["location"],
            "person": stephanie["name"],
            "start_time": minutes_to_time_str(stephanie_start),
            "end_time": minutes_to_time_str(stephanie_end)
        })
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{int(hours):02d}:{int(minutes):02d}"

if __name__ == "__main__":
    main()