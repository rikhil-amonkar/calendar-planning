#!/usr/bin/env python3
import json

def time_str_to_minutes(time_str):
    # Converts a time string like "9:00" into total minutes since midnight.
    parts = time_str.split(":")
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time_str(minutes):
    # Converts total minutes since midnight to a time string in H:MM format.
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def compute_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"  # Arrival at Russian Hill
    travel_time_RH_to_PH = 7  # in minutes (Russian Hill to Pacific Heights)
    travel_time_PH_to_RH = 7  # in minutes (Pacific Heights to Russian Hill) - not used in meeting scheduling
    
    # Barbara's available time and meeting requirements
    barbara_location = "Pacific Heights"
    barbara_available_start = "7:15"
    barbara_available_end = "22:00"
    meeting_min_duration = 60  # in minutes
    
    # Convert times to minutes
    arrival_minutes = time_str_to_minutes(arrival_time)
    barbara_start_minutes = time_str_to_minutes(barbara_available_start)
    barbara_end_minutes = time_str_to_minutes(barbara_available_end)
    
    # Compute travel: leave Russian Hill immediately, arrival at Pacific Heights:
    arrival_at_PH = arrival_minutes + travel_time_RH_to_PH
    
    # The meeting with Barbara can only start when both you have arrived and Barbara is available.
    meeting_start = max(arrival_at_PH, barbara_start_minutes)
    meeting_end = meeting_start + meeting_min_duration
    
    # Ensure that the meeting finishes before Barbara leaves.
    if meeting_end > barbara_end_minutes:
        raise ValueError("Cannot schedule a meeting with Barbara that satisfies the time constraints.")
    
    # Construct the itinerary.
    # Since the goal is to meet as many friends as possible and only Barbara is provided,
    # the optimal schedule is to meet her once at Pacific Heights.
    itinerary = [
        {
            "action": "meet",
            "location": barbara_location,
            "person": "Barbara",
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        }
    ]
    
    # Build the output dictionary
    schedule = {
        "itinerary": itinerary
    }
    return schedule

if __name__ == "__main__":
    schedule = compute_optimal_schedule()
    print(json.dumps(schedule))