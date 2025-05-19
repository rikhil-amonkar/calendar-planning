#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def minutes_to_time_str(minutes):
    # Convert minutes since midnight to H:MM 24-hour format (no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters (all times in minutes since midnight)
    # Arrival time at Embarcadero at 9:00AM = 540 minutes
    start_time = 9 * 60  # 540 minutes
    
    # Travel times (in minutes)
    travel = {
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Alamo Square"): 17,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Financial District"): 17
    }
    
    # Meeting constraints and desired durations (in minutes)
    # Stephanie is available at Financial District from 8:15AM to 11:30AM
    stephanie_available_start = 8 * 60 + 15  # 8:15AM = 495 minutes
    stephanie_available_end   = 11 * 60 + 30   # 11:30AM = 690 minutes
    stephanie_meet_duration   = 90

    # John is available at Alamo Square from 10:15AM to 8:45PM
    john_available_start = 10 * 60 + 15  # 10:15AM = 615 minutes
    john_available_end   = 20 * 60 + 45    # 8:45PM = 1245 minutes
    john_meet_duration   = 30

    # We assume the optimal schedule is to meet Stephanie first then John.
    # Compute schedule:
    # 1. Travel from Embarcadero to Financial District:
    depart_location = "Embarcadero"
    stephanie_location = "Financial District"
    travel_time_to_stephanie = travel[(depart_location, stephanie_location)]
    arrival_stephanie = start_time + travel_time_to_stephanie
    # Meeting with Stephanie can start at the later of our arrival or her available start
    stephanie_meet_start = max(arrival_stephanie, stephanie_available_start)
    stephanie_meet_end = stephanie_meet_start + stephanie_meet_duration
    # Ensure that the end time does not exceed her available end time.
    if stephanie_meet_end > stephanie_available_end:
        raise ValueError("Cannot meet Stephanie for the required duration within her available window.")

    # 2. Travel from Financial District to Alamo Square for John
    john_location = "Alamo Square"
    travel_time_to_john = travel[(stephanie_location, john_location)]
    arrival_john = stephanie_meet_end + travel_time_to_john
    john_meet_start = max(arrival_john, john_available_start)
    john_meet_end = john_meet_start + john_meet_duration
    # Ensure that meeting John does not exceed his available end time.
    if john_meet_end > john_available_end:
        raise ValueError("Cannot meet John for the required duration within his available window.")

    # Construct itinerary
    itinerary = [
        {
            "action": "meet",
            "location": stephanie_location,
            "person": "Stephanie",
            "start_time": minutes_to_time_str(stephanie_meet_start),
            "end_time": minutes_to_time_str(stephanie_meet_end)
        },
        {
            "action": "meet",
            "location": john_location,
            "person": "John",
            "start_time": minutes_to_time_str(john_meet_start),
            "end_time": minutes_to_time_str(john_meet_end)
        }
    ]

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()