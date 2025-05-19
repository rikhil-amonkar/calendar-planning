#!/usr/bin/env python3
import json

def time_to_minutes(time_str):
    # Converts time string "H:MM" to minutes since midnight.
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    # Converts minutes since midnight to "H:MM" (24-hour format, no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times dictionary (in minutes)
    travel = {
        "Union Square": {
            "Golden Gate Park": 22,
            "Pacific Heights": 15,
            "Presidio": 24,
            "Chinatown": 7,
            "The Castro": 19
        },
        "Golden Gate Park": {
            "Union Square": 22,
            "Pacific Heights": 16,
            "Presidio": 11,
            "Chinatown": 23,
            "The Castro": 13
        },
        "Pacific Heights": {
            "Union Square": 12,
            "Golden Gate Park": 15,
            "Presidio": 11,
            "Chinatown": 11,
            "The Castro": 16
        },
        "Presidio": {
            "Union Square": 22,
            "Golden Gate Park": 12,
            "Pacific Heights": 11,
            "Chinatown": 21,
            "The Castro": 21
        },
        "Chinatown": {
            "Union Square": 7,
            "Golden Gate Park": 23,
            "Pacific Heights": 10,
            "Presidio": 19,
            "The Castro": 22
        },
        "The Castro": {
            "Union Square": 19,
            "Golden Gate Park": 11,
            "Pacific Heights": 16,
            "Presidio": 20,
            "Chinatown": 20
        }
    }
    
    # Meeting constraints for friends.
    # Each friend is represented as a dict with location, available window and required meeting duration in minutes.
    meetings = [
        {
            "person": "Robert",
            "location": "The Castro",
            "available_start": "8:30",
            "available_end": "14:15",
            "duration": 30
        },
        {
            "person": "Andrew",
            "location": "Golden Gate Park",
            "available_start": "11:45",
            "available_end": "14:30",
            "duration": 75
        },
        {
            "person": "Rebecca",
            "location": "Chinatown",
            "available_start": "9:45",
            "available_end": "21:30",
            "duration": 90
        },
        {
            "person": "Sarah",
            "location": "Pacific Heights",
            "available_start": "16:15",
            "available_end": "18:45",
            "duration": 15
        },
        {
            "person": "Nancy",
            "location": "Presidio",
            "available_start": "17:30",
            "available_end": "19:15",
            "duration": 60
        }
    ]
    
    # Our chosen ordering based on feasibility and minimizing waiting times.
    # Starting location and time.
    current_location = "Union Square"
    current_time = time_to_minutes("9:00")
    
    itinerary = []
    
    for meeting in meetings:
        # Calculate travel time from current location to meeting location.
        travel_time = travel[current_location][meeting["location"]]
        # Arrival time at the meeting location.
        arrival_time = current_time + travel_time
        # Convert available start time of the meeting to minutes.
        available_start = time_to_minutes(meeting["available_start"])
        available_end = time_to_minutes(meeting["available_end"])
        
        # The meeting can only start when friend is available.
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + meeting["duration"]
        
        # Check if meeting can be finished within the available window.
        if meeting_end > available_end:
            # If not feasible, print error (in a real scenario we might try alternative ordering)
            raise ValueError(f"Cannot schedule meeting with {meeting['person']} within available window.")
        
        # Append meeting to itinerary.
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location after meeting.
        current_time = meeting_end
        current_location = meeting["location"]
    
    # Create final schedule dictionary.
    schedule = {"itinerary": itinerary}
    
    # Output the schedule as JSON-formatted dictionary.
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()