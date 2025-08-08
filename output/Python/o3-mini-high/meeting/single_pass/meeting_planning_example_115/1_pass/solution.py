#!/usr/bin/env python3
import json

def minutes_to_time(minutes):
    # Convert minutes since midnight to "H:MM" 24-hour format (no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Arrival time at Richmond District: 9:00 AM (in minutes since midnight)
    arrival_time = 9 * 60  # 540 minutes
    starting_location = "Richmond District"
    
    # Define travel times in minutes between locations (as provided)
    travel_times = {
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Marina District"): 6,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7
    }
    
    # Meeting constraints for Carol
    # Carol is available in Marina District from 11:30 (690) to 15:00 (900) with a minimum meeting duration of 60 minutes.
    carol_location = "Marina District"
    carol_avail_start = 11 * 60 + 30  # 690 minutes => 11:30
    carol_avail_end = 15 * 60         # 900 minutes => 15:00
    carol_min_duration = 60           # 60 minutes minimum
    
    # Meeting constraints for Jessica
    # Jessica is available in Pacific Heights from 15:30 (930) to 16:45 (1005) with a minimum meeting duration of 45 minutes.
    jessica_location = "Pacific Heights"
    jessica_avail_start = 15 * 60 + 30  # 930 minutes => 15:30
    jessica_avail_end = 16 * 60 + 45    # 1005 minutes => 16:45
    jessica_min_duration = 45           # 45 minutes minimum
    
    itinerary = []
    current_time = arrival_time
    current_location = starting_location
    
    # Schedule meeting with Carol
    # Compute departure time from current location (Richmond District) to Marina District such that arrival is not before Carol's availability.
    travel_time_to_carol = travel_times[(current_location, carol_location)]
    # To arrive exactly at Carol's availability start (11:30), one would depart at:
    ideal_departure_for_carol = carol_avail_start - travel_time_to_carol
    # However, if we're not there yet, we must depart no earlier than our arrival time.
    departure_for_carol = max(current_time, ideal_departure_for_carol)
    arrival_at_carol = departure_for_carol + travel_time_to_carol
    # The meeting can only start when Carol is available.
    carol_meeting_start = max(arrival_at_carol, carol_avail_start)
    carol_meeting_end = carol_meeting_start + carol_min_duration
    # Ensure that the meeting fits within Carol's available window.
    if carol_meeting_end <= carol_avail_end:
        itinerary.append({
            "action": "meet",
            "location": carol_location,
            "person": "Carol",
            "start_time": minutes_to_time(carol_meeting_start),
            "end_time": minutes_to_time(carol_meeting_end)
        })
        # Update current time and location after meeting Carol.
        current_time = carol_meeting_end
        current_location = carol_location
    else:
        # If the meeting with Carol isn't possible, we remain at the current location.
        pass

    # Schedule meeting with Jessica
    travel_time_to_jessica = travel_times[(current_location, jessica_location)]
    arrival_at_jessica = current_time + travel_time_to_jessica
    jessica_meeting_start = max(arrival_at_jessica, jessica_avail_start)
    jessica_meeting_end = jessica_meeting_start + jessica_min_duration
    # Ensure that the meeting with Jessica fits within her available window.
    if jessica_meeting_end <= jessica_avail_end:
        itinerary.append({
            "action": "meet",
            "location": jessica_location,
            "person": "Jessica",
            "start_time": minutes_to_time(jessica_meeting_start),
            "end_time": minutes_to_time(jessica_meeting_end)
        })
    
    # Prepare the result as a JSON-formatted dictionary.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()