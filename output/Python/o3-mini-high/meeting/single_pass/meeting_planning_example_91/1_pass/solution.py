#!/usr/bin/env python3
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters
    arrival_time_str = "9:00"
    # Convert arrival time 9:00 to minutes from midnight (9*60 = 540)
    arrival_time_minutes = 9 * 60  # 540 minutes
    
    starting_location = "Russian Hill"
    
    # Travel times in minutes
    travel_time_rh_to_rd = 14  # Russian Hill to Richmond District
    travel_time_rd_to_rh = 13  # Richmond District to Russian Hill
    
    # Daniel's meeting constraints at Richmond District: available from 19:00 to 20:15
    daniel_location = "Richmond District"
    daniel_avail_start_str = "19:00"  # 7:00 PM in 24-hour format
    daniel_avail_end_str = "20:15"    # 8:15 PM in 24-hour format
    
    # Convert Daniel's available times to minutes from midnight
    daniel_avail_start_minutes = 19 * 60          # 1140 minutes (19:00)
    daniel_avail_end_minutes = 20 * 60 + 15         # 1215 minutes (20:15)
    
    # Required meeting duration with Daniel (in minutes)
    required_meeting_duration = 75  # 75 minutes
    
    # Check if Daniel's available window is sufficient
    if daniel_avail_end_minutes - daniel_avail_start_minutes < required_meeting_duration:
        raise ValueError("Daniel's available window is shorter than the required meeting duration.")
    
    # For an optimal schedule to get the full required meeting time,
    # we schedule the meeting at Daniel's earliest available time.
    meeting_start_minutes = daniel_avail_start_minutes  # 19:00 start
    meeting_end_minutes = meeting_start_minutes + required_meeting_duration  # 20:15 end
    
    # Calculate the departure time from Russian Hill required to reach Richmond District by 19:00.
    departure_from_rh_minutes = meeting_start_minutes - travel_time_rh_to_rd  # 1140 - 14 = 1126 minutes
    
    # Validate that the departure time is not before arrival time at Russian Hill
    if departure_from_rh_minutes < arrival_time_minutes:
        raise ValueError("Not enough time between arrival and departure for meeting.")
    
    # At this point, the day includes: arriving at Russian Hill at 9:00,
    # spending time until 18:46 (calculated departure time) at Russian Hill,
    # traveling for 14 minutes to arrive at Richmond District by 19:00,
    # and then meeting Daniel from 19:00 to 20:15 (75 minutes as required).
    
    # Construct the itinerary with the meeting event with Daniel.
    itinerary = []
    meeting_event = {
        "action": "meet",
        "location": daniel_location,
        "person": "Daniel",
        "start_time": minutes_to_time_str(meeting_start_minutes),
        "end_time": minutes_to_time_str(meeting_end_minutes)
    }
    itinerary.append(meeting_event)
    
    # Prepare the final output structure in JSON format.
    output = {
        "itinerary": itinerary
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()