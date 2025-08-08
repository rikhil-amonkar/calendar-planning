#!/usr/bin/env python3
import json

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times in minutes between locations
    travel_times = {
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Russian Hill"): 13,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11
    }
    
    # Arrival at North Beach at 9:00AM (9*60 = 540 minutes)
    arrival_north_beach = 9 * 60  # 540 minutes
    
    # Emily's meeting constraints at Union Square:
    # Available from 16:00 (960 minutes) to 17:15 (1035 minutes)
    # Meeting duration requirement: at least 45 minutes
    emily_location = "Union Square"
    emily_available_start = 16 * 60         # 960 minutes => 16:00
    emily_available_end = 17 * 60 + 15        # 1035 minutes => 17:15
    emily_min_duration = 45                 # minutes
    
    # Margaret's meeting constraints at Russian Hill:
    # Available from 19:00 (1140 minutes) to 21:00 (1260 minutes)
    # Meeting duration requirement: at least 120 minutes
    margaret_location = "Russian Hill"
    margaret_available_start = 19 * 60        # 1140 minutes => 19:00
    margaret_available_end = 21 * 60          # 1260 minutes => 21:00
    margaret_min_duration = 120              # minutes
    
    # Calculate when to leave North Beach to arrive at Union Square by Emily's available start.
    travel_nb_to_us = travel_times[("North Beach", "Union Square")]
    departure_from_nb_for_emily = emily_available_start - travel_nb_to_us
    # (We arrive at North Beach at 9:00 and wait until departure_from_nb_for_emily)
    
    # Schedule meeting with Emily:
    # For simplicity, we start the meeting at the earliest available time.
    emily_meet_start = emily_available_start  # 16:00 (960 minutes)
    emily_meet_end = emily_meet_start + emily_min_duration  # 16:45 (1005 minutes)
    # Ensure that the meeting ends before Emily leaves (1005 <= 1035)
    
    # After meeting Emily, travel from Union Square to Russian Hill.
    travel_us_to_rh = travel_times[("Union Square", "Russian Hill")]
    departure_from_us = emily_meet_end  # leave immediately after Emily meeting
    arrival_at_rh = departure_from_us + travel_us_to_rh  # arrival time at Russian Hill
    
    # Since Margaret is available starting at 19:00 (1140 minutes),
    # wait until that time if arriving earlier.
    margaret_meet_start = max(arrival_at_rh, margaret_available_start)
    margaret_meet_end = margaret_meet_start + margaret_min_duration
    # This should exactly fit into Margaret's available window.
    
    itinerary = [
        {
            "action": "meet",
            "location": emily_location,
            "person": "Emily",
            "start_time": minutes_to_time(emily_meet_start),
            "end_time": minutes_to_time(emily_meet_end)
        },
        {
            "action": "meet",
            "location": margaret_location,
            "person": "Margaret",
            "start_time": minutes_to_time(margaret_meet_start),
            "end_time": minutes_to_time(margaret_meet_end)
        }
    ]
    
    schedule = {"itinerary": itinerary}
    print(json.dumps(schedule))
    
if __name__ == "__main__":
    main()