#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def minutes_to_time_str(total_minutes):
    # Convert minutes since midnight to H:MM format without leading zero for hour.
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Input parameters (all times in minutes since midnight)
    
    # Arrival at Russian Hill at 9:00AM -> 9*60 = 540 minutes
    arrival_russian_hill = 9 * 60  # 540
    
    # Daniel will be at Richmond District from 7:00PM (19:00) to 8:15PM (20:15)
    daniel_available_start = 19 * 60      # 1140 minutes
    daniel_available_end = 20 * 60 + 15     # 1215 minutes
    
    # Travel times in minutes
    travel_rh_to_rd = 14   # Russian Hill to Richmond District
    travel_rd_to_rh = 13   # Richmond District to Russian Hill
    
    # To maximize meeting time with Daniel (minimum 75 minutes) and meet his constraints:
    # We need to arrive exactly at his available starting time.
    # So compute the departure time from Russian Hill:
    departure_from_russian_hill = daniel_available_start - travel_rh_to_rd  # 1140 - 14 = 1126 minutes
    
    # Check that departure time is after arrival time
    if departure_from_russian_hill < arrival_russian_hill:
        raise ValueError("Not enough time to depart from Russian Hill based on arrival time!")
    
    # The meeting with Daniel will be scheduled starting at daniel_available_start
    # and must last at least 75 minutes. In Daniel's time window from 19:00 to 20:15,
    # there are exactly 75 minutes available.
    meeting_duration = daniel_available_end - daniel_available_start
    if meeting_duration < 75:
        raise ValueError("Meeting duration does not meet the minimum required time!")
    
    # Compute times as strings.
    departure_time_str = minutes_to_time_str(departure_from_russian_hill)
    meeting_start_str = minutes_to_time_str(daniel_available_start)
    meeting_end_str = minutes_to_time_str(daniel_available_end)
    
    # Create itinerary:
    # Although travel periods are important for planning, the problem instruction requests
    # "meet" actions be included in the output JSON.
    # Hence, we include only the meeting with Daniel.
    itinerary = [
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Daniel",
            "start_time": meeting_start_str,
            "end_time": meeting_end_str
        }
    ]
    
    # Construct the final schedule dictionary.
    schedule = {
        "itinerary": itinerary
    }
    
    # Output the result as JSON.
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()