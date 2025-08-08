#!/usr/bin/env python3
import json

def time_to_minutes(time_str):
    # Convert "H:MM" 24-hour format to minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Convert minutes since midnight to "H:MM" (no leading zero for hour)
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Define travel times (in minutes) between locations
    travel_times = {
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Bayview"): 22,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Fisherman's Wharf"): 25
    }
    
    # Define friends and their meeting constraints
    friends = [
        {
            "person": "Helen",
            "location": "North Beach",
            "available_start": time_to_minutes("7:00"),
            "available_end": time_to_minutes("16:45"),
            "meeting_duration": 120
        },
        {
            "person": "Kimberly",
            "location": "Fisherman's Wharf",
            "available_start": time_to_minutes("16:30"),
            "available_end": time_to_minutes("21:00"),
            "meeting_duration": 45
        },
        {
            "person": "Patricia",
            "location": "Bayview",
            "available_start": time_to_minutes("18:00"),
            "available_end": time_to_minutes("21:15"),
            "meeting_duration": 120
        }
    ]
    
    # Starting point: Arrive at Nob Hill at 9:00
    current_location = "Nob Hill"
    current_time = time_to_minutes("9:00")
    
    itinerary = []
    
    # Process each friend's meeting in order
    for friend in friends:
        # Add travel time if current location is not the friend's location
        if current_location != friend["location"]:
            travel_key = (current_location, friend["location"])
            travel_duration = travel_times.get(travel_key, 0)
            current_time += travel_duration
        
        # The meeting starts at the later of arrival time and friend's available start time
        meeting_start = max(current_time, friend["available_start"])
        meeting_end = meeting_start + friend["meeting_duration"]
        
        # Check if meeting can be scheduled within friend's available window
        if meeting_end > friend["available_end"]:
            # If not possible, skip scheduling for this friend.
            continue
        
        # Append the meeting to the itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location after meeting
        current_time = meeting_end
        current_location = friend["location"]
    
    # Prepare result in the required JSON format.
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result))
    
if __name__ == "__main__":
    main()