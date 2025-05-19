#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper function to convert minutes since midnight to "H:MM" 24-hour string format.
def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Meeting parameters (times in minutes)
    # Start time: 9:00 AM -> 9 * 60 = 540 minutes since midnight
    start_time = 9 * 60  # 540
    
    # Travel times in minutes between locations (as given):
    travel_times = {
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Mission District"): 26,
        
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Mission District"): 17,
        
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Mission District"): 13,
        
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Mission District"): 18,
        
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Mission District"): 18,
        
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "North Beach"): 17,
    }
    
    # Participants' constraints:
    # Each person is represented as a dictionary:
    # "location": where the person will be,
    # "available_start": when they are available (in minutes since midnight),
    # "available_end": when they are no longer available,
    # "min_duration": required meeting duration in minutes.
    meetings = {
        "Jessica": {"location": "Golden Gate Park", "available_start": 13*60+45, "available_end": 15*60, "min_duration": 30},
        "Ashley": {"location": "Bayview", "available_start": 17*60+15, "available_end": 20*60, "min_duration": 105},
        "Ronald": {"location": "Chinatown", "available_start": 7*60+15, "available_end": 14*60+45, "min_duration": 90},
        "William": {"location": "North Beach", "available_start": 13*60+15, "available_end": 20*60+15, "min_duration": 15},
        "Daniel": {"location": "Mission District", "available_start": 7*60, "available_end": 11*60+15, "min_duration": 105},
    }
    
    itinerary = []  # To store the scheduled meetings
    
    current_time = start_time
    current_location = "Presidio"
    
    # We will build the schedule in the following order:
    # 1. Daniel at Mission District
    # 2. Ronald at Chinatown
    # 3. Jessica at Golden Gate Park
    # 4. William at North Beach
    # 5. Ashley at Bayview
    #
    # The schedule is computed so that we account for travel and waiting times.
    
    # 1. Daniel meeting: Travel from Presidio to Mission District
    travel = travel_times[(current_location, meetings["Daniel"]["location"])]
    current_time += travel  # arrive at Mission District
    meeting_start = max(current_time, meetings["Daniel"]["available_start"])
    # For Daniel, we must finish by his available_end and provide min_duration.
    meeting_end = meeting_start + meetings["Daniel"]["min_duration"]
    # Ensure meeting finishes before Daniel's availability end (11:15 -> 675)
    if meeting_end > meetings["Daniel"]["available_end"]:
        raise ValueError("Cannot schedule Daniel meeting within available time.")
    itinerary.append({
        "action": "meet",
        "location": meetings["Daniel"]["location"],
        "person": "Daniel",
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })
    current_time = meeting_end
    current_location = meetings["Daniel"]["location"]
    
    # 2. Ronald meeting: Travel from Mission District to Chinatown
    travel = travel_times[(current_location, meetings["Ronald"]["location"])]
    current_time += travel  # travel time to Chinatown
    meeting_start = max(current_time, meetings["Ronald"]["available_start"])
    meeting_end = meeting_start + meetings["Ronald"]["min_duration"]
    if meeting_end > meetings["Ronald"]["available_end"]:
        raise ValueError("Cannot schedule Ronald meeting within available time.")
    itinerary.append({
        "action": "meet",
        "location": meetings["Ronald"]["location"],
        "person": "Ronald",
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })
    current_time = meeting_end
    current_location = meetings["Ronald"]["location"]
    
    # 3. Jessica meeting: Travel from Chinatown to Golden Gate Park
    travel = travel_times[(current_location, meetings["Jessica"]["location"])]
    current_time += travel  # travel to Golden Gate Park
    # Jessica available_start is 13:45, so if we arrive earlier, we wait.
    meeting_start = max(current_time, meetings["Jessica"]["available_start"])
    meeting_end = meeting_start + meetings["Jessica"]["min_duration"]
    if meeting_end > meetings["Jessica"]["available_end"]:
        raise ValueError("Cannot schedule Jessica meeting within available time.")
    itinerary.append({
        "action": "meet",
        "location": meetings["Jessica"]["location"],
        "person": "Jessica",
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })
    current_time = meeting_end
    current_location = meetings["Jessica"]["location"]
    
    # 4. William meeting: Travel from Golden Gate Park to North Beach
    travel = travel_times[(current_location, meetings["William"]["location"])]
    current_time += travel  # travel to North Beach
    meeting_start = max(current_time, meetings["William"]["available_start"])
    meeting_end = meeting_start + meetings["William"]["min_duration"]
    if meeting_end > meetings["William"]["available_end"]:
        raise ValueError("Cannot schedule William meeting within available time.")
    itinerary.append({
        "action": "meet",
        "location": meetings["William"]["location"],
        "person": "William",
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })
    # For Ashley meeting, we may need to wait until a specific departure time.
    # Current location becomes North Beach.
    current_location = meetings["William"]["location"]
    
    # 5. Ashley meeting: We want to arrive at Bayview exactly at her available_start 17:15.
    desired_arrival = meetings["Ashley"]["available_start"]  # 17:15 in minutes
    # Travel from North Beach to Bayview:
    travel = travel_times[(current_location, meetings["Ashley"]["location"])]
    # Calculate when we need to leave to arrive exactly at desired_arrival:
    departure_time_needed = desired_arrival - travel
    # If current_time is earlier than departure_time_needed, wait until then.
    if current_time < departure_time_needed:
        current_time = departure_time_needed
    # Travel:
    current_time += travel  # arrive at Bayview (should be desired_arrival)
    meeting_start = max(current_time, meetings["Ashley"]["available_start"])
    meeting_end = meeting_start + meetings["Ashley"]["min_duration"]
    if meeting_end > meetings["Ashley"]["available_end"]:
        raise ValueError("Cannot schedule Ashley meeting within available time.")
    itinerary.append({
        "action": "meet",
        "location": meetings["Ashley"]["location"],
        "person": "Ashley",
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    })
    
    # Build final JSON result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
    
if __name__ == "__main__":
    main()