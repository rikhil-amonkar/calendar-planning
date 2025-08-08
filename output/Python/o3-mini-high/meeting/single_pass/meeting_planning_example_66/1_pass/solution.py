#!/usr/bin/env python3
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters (all times in minutes after midnight)
    # You arrive at Nob Hill at 9:00AM => 9*60 = 540 minutes
    arrival_nob_hill = 9 * 60  # 540
    
    # Robert's availability at Presidio: 11:15AM to 5:45PM
    robert_available_start = 11 * 60 + 15  # 675 minutes
    robert_available_end   = 17 * 60 + 45   # 1065 minutes
    
    # Travel times in minutes
    travel_nobhill_to_presidio = 17
    travel_presidio_to_nobhill = 18
    
    # To maximize number of friend meetings,
    # we assume you can meet one local friend at Nob Hill in the morning,
    # then travel to meet Robert.
    #
    # For the meeting with Robert, you need a minimum of 120 minutes.
    # Also, you want to time your departure from Nob Hill so that you arrive
    # at Presidio right when Robert becomes available.
    #
    # Calculate departure time from Nob Hill:
    departure_nob_hill = robert_available_start - travel_nobhill_to_presidio  # Must leave by this time.
    # Schedule morning meeting with a friend (Alice) at Nob Hill from arrival time until departure.
    alice_meet_start = arrival_nob_hill          # 9:00AM -> 540 minutes
    alice_meet_end   = departure_nob_hill          # Time to leave for Presidio
    
    # Calculate arrival time at Presidio (should equal Robert's available start)
    arrival_presidio = departure_nob_hill + travel_nobhill_to_presidio  # should be 675 (11:15AM)
    
    # Schedule meeting with Robert.
    # We schedule the meeting for the minimum required 120 minutes.
    robert_meet_start = max(arrival_presidio, robert_available_start)   # 11:15AM (675 minutes)
    robert_meet_duration = 120  # minimum required minutes
    robert_meet_end = robert_meet_start + robert_meet_duration            # 675 + 120 = 795 minutes (13:15)
    
    # (Note: After meeting Robert, you would travel back to Nob Hill,
    # arriving at robert_meet_end + travel_presidio_to_nobhill.
    # That travel is accounted for but not scheduled as a meeting.)
    
    # Build the itinerary.
    itinerary = [
        {
            "action": "meet",
            "location": "Nob Hill",
            "person": "Alice",
            "start_time": minutes_to_time_str(alice_meet_start),
            "end_time": minutes_to_time_str(alice_meet_end)
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": minutes_to_time_str(robert_meet_start),
            "end_time": minutes_to_time_str(robert_meet_end)
        }
    ]
    
    schedule = {"itinerary": itinerary}
    
    # Output the result as JSON-formatted dictionary.
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()