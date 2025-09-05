import json
from datetime import datetime, timedelta

def format_time(dt):
    # Formats the datetime dt as H:MM in 24-hour format with no leading zero for the hour.
    return f"{dt.hour}:{dt.minute:02d}"

def main():
    # Input parameters
    travel_time_gp_to_ct = 23  # minutes from Golden Gate Park to Chinatown
    travel_time_ct_to_gp = 23  # minutes from Chinatown to Golden Gate Park (not used in current schedule)
    
    # Arrival and availability times (using an arbitrary fixed date)
    gp_arrival = datetime(2023, 1, 1, 9, 0)  # Arrive at Golden Gate Park at 9:00
    david_available_start = datetime(2023, 1, 1, 16, 0)  # David available from 16:00 (4:00PM)
    david_available_end = datetime(2023, 1, 1, 21, 45)   # to 21:45 (9:45PM)
    required_meeting_duration = timedelta(minutes=105)     # Need at least 105 minutes with David

    # To take full advantage of the available time and maximize friend meetings,
    # we assume you meet a friend "Alice" at Golden Gate Park from arrival until you must leave
    # to travel to Chinatown arriving when David becomes available.
    # Compute the departure time from Golden Gate Park:
    departure_from_gp = david_available_start - timedelta(minutes=travel_time_gp_to_ct)
    
    # Define meeting with friend "Alice" at Golden Gate Park.
    meeting_alice_start = gp_arrival
    meeting_alice_end = departure_from_gp
    
    # Travel: departing from Golden Gate Park at meeting_alice_end,
    # you arrive at Chinatown exactly at david_available_start.
    arrival_at_chinatown = meeting_alice_end + timedelta(minutes=travel_time_gp_to_ct)
    
    # Schedule meeting with David.
    meeting_david_start = arrival_at_chinatown
    meeting_david_end = meeting_david_start + required_meeting_duration
    
    # If the meeting with David would extend past his available time, adjust accordingly.
    if meeting_david_end > david_available_end:
        meeting_david_start = david_available_end - required_meeting_duration
        meeting_david_end = david_available_end
        # Recompute departure from GP to ensure proper travel timing.
        departure_from_gp = meeting_david_start - timedelta(minutes=travel_time_gp_to_ct)
        meeting_alice_end = departure_from_gp
        arrival_at_chinatown = meeting_david_start

    # Create the itinerary as a list of meeting events.
    itinerary = [
        {
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Alice",
            "start_time": format_time(meeting_alice_start),
            "end_time": format_time(meeting_alice_end)
        },
        {
            "action": "meet",
            "location": "Chinatown",
            "person": "David",
            "start_time": format_time(meeting_david_start),
            "end_time": format_time(meeting_david_end)
        }
    ]
    
    # Build the final schedule dictionary.
    schedule = {"itinerary": itinerary}
    
    # Output the result as a JSON-formatted dictionary.
    print(json.dumps(schedule, indent=2))

if __name__ == '__main__':
    main()