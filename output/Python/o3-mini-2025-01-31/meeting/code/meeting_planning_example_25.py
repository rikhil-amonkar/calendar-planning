#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def time_to_str(dt):
    # Format time as H:MM without leading zero in hour.
    return dt.strftime("%-H:%M") if dt.strftime("%-H") != "" else dt.strftime("%H:%M")

def main():
    # Input parameters
    arrival_location = "Golden Gate Park"
    meeting_location = "Chinatown"
    friend = "David"
    
    # Times in 24-hour format. Reference date is arbitrary; we'll use today.
    base_date = datetime.today().replace(hour=0, minute=0, second=0, microsecond=0)
    
    # You arrive at Golden Gate Park at 9:00AM.
    arrival_time = base_date.replace(hour=9, minute=0)
    
    # David will be at Chinatown from 16:00 to 21:45.
    david_available_start = base_date.replace(hour=16, minute=0)
    david_available_end = base_date.replace(hour=21, minute=45)
    
    # Travel distance in minutes (Golden Gate Park to Chinatown)
    travel_minutes = 23
    travel_duration = timedelta(minutes=travel_minutes)
    
    # Minimum meeting duration (105 minutes)
    min_meeting_duration = timedelta(minutes=105)
    
    # To meet David at the beginning of his availability, plan to arrive at Chinatown at 16:00.
    # Therefore, we need to leave Golden Gate Park at:
    departure_time = david_available_start - travel_duration
    
    # Ensure that departure time is not before arrival time.
    if departure_time < arrival_time:
        # If it is, adjust the meeting start time.
        departure_time = arrival_time
        david_meeting_start = departure_time + travel_duration
    else:
        david_meeting_start = david_available_start
    
    # Calculate meeting end time by adding the minimum meeting duration.
    david_meeting_end = david_meeting_start + min_meeting_duration
    
    # Make sure meeting end time is within David's availability.
    if david_meeting_end > david_available_end:
        # If not possible, adjust meeting end to David's available end.
        david_meeting_end = david_available_end
        # And adjust meeting start time accordingly if possible.
        if david_meeting_end - min_meeting_duration >= david_available_start:
            david_meeting_start = david_meeting_end - min_meeting_duration
        else:
            # Cannot meet the minimum duration, so exit with an error itinerary.
            result = {
                "itinerary": [
                    {"action": "error", "message": "Meeting time with David cannot satisfy the minimum duration given his availability."}
                ]
            }
            print(json.dumps(result))
            return
    
    # Create itinerary events.
    # The schedule includes a travel leg from Golden Gate Park to Chinatown and a meeting with David.
    # However, as per output structure, we output meeting events.
    # We assume waiting or travel are not separate "meet" events.
    itinerary = []
    
    # Meeting event with David in Chinatown.
    itinerary.append({
        "action": "meet",
        "location": meeting_location,
        "person": friend,
        "start_time": time_to_str(david_meeting_start),
        "end_time": time_to_str(david_meeting_end)
    })
    
    # Prepare final schedule.
    schedule = {
        "itinerary": itinerary
    }
    
    # Output the result as JSON.
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()