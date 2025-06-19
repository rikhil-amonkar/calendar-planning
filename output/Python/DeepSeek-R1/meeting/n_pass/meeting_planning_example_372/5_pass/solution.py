import json
from itertools import permutations

def main():
    # Original travel times (asymmetric)
    original_travel_times = {
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
    
    # Create symmetric travel times by averaging
    locations = list(original_travel_times.keys())
    travel_times = {loc: {} for loc in locations}
    for i, loc1 in enumerate(locations):
        for loc2 in locations[i+1:]:
            time1 = original_travel_times[loc1][loc2]
            time2 = original_travel_times[loc2][loc1]
            avg = round((time1 + time2) / 2)
            travel_times[loc1][loc2] = avg
            travel_times[loc2][loc1] = avg
    
    # Define friends with their constraints
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
    
    # Calculate constraint for Charles from Stephanie
    travel_to_stephanie = travel_times[charles["location"]][stephanie["location"]]
    charles_latest_start = stephanie["available_start"] - travel_to_stephanie - charles["min_duration"]
    
    candidates = []
    for perm in permutations(friends):
        current_location = start_location
        current_time = start_time
        schedule_morning = []
        travel_time_total = 0
        valid = True
        
        for friend in perm:
            tt = travel_times[current_location][friend["location"]]
            travel_time_total += tt
            current_time += tt  # arrival time
            
            meeting_start = max(current_time, friend["available_start"])
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
        
        # Travel to Charles
        tt_to_charles = travel_times[current_location][charles["location"]]
        travel_time_total += tt_to_charles
        arrival_charles = current_time + tt_to_charles
        
        # Must arrive by charles_latest_start to meet Stephanie on time
        if arrival_charles > charles_latest_start:
            continue
        
        # Also account for travel to Stephanie
        total_travel = travel_time_total + travel_to_stephanie
        candidates.append({
            "total_travel": total_travel,
            "schedule": schedule_morning,
            "arrival_charles": arrival_charles,
            "last_location": current_location
        })
    
    if not candidates:
        itinerary = []
    else:
        best_candidate = min(candidates, key=lambda x: x["total_travel"])
        itinerary = []
        
        # Add morning meetings
        for meeting in best_candidate["schedule"]:
            friend = meeting["friend"]
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting["start"]),
                "end_time": minutes_to_time_str(meeting["end"])
            })
        
        # Schedule Charles to end at 20:20 for Stephanie
        charles_start = min(
            max(best_candidate["arrival_charles"], charles["available_start"]),
            charles_latest_start
        )
        charles_end = charles_start + charles["min_duration"]
        itinerary.append({
            "action": "meet",
            "location": charles["location"],
            "person": charles["name"],
            "start_time": minutes_to_time_str(charles_start),
            "end_time": minutes_to_time_str(charles_end)
        })
        
        # Stephanie's meeting starts exactly at 20:30
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