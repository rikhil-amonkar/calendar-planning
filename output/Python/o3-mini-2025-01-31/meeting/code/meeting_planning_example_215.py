#!/usr/bin/env python3
import json
import itertools

def minutes_to_str(m):
    # convert minutes since midnight to "H:MM" 24-hour format (without leading zero for hour)
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def compute_schedule(start_location, start_time, friends, travel_times, order):
    itinerary = []
    current_location = start_location
    current_time = start_time
    valid = True
    total_meetings = 0
    
    # For each friend in the given order
    for friend in order:
        # Calculate travel time from current location to friend's meeting location.
        if current_location == friend['location']:
            travel = 0
        else:
            travel = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel
        # If arriving before availability, must wait until friend is available.
        meeting_start = max(arrival_time, friend['avail_start'])
        meeting_end = meeting_start + friend['min_meeting']
        # Check if meeting fits within friend's availability window.
        if meeting_end > friend['avail_end']:
            valid = False
            break
        # Append meeting record to itinerary.
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['person'],
            "start_time": minutes_to_str(meeting_start),
            "end_time": minutes_to_str(meeting_end)
        })
        # Update current time and location.
        current_time = meeting_end
        current_location = friend['location']
        total_meetings += 1
    return valid, itinerary, current_time

def main():
    # Define travel times (in minutes) as a nested dictionary.
    travel_times = {
        "Bayview": {
            "Embarcadero": 19,
            "Richmond District": 25,
            "Fisherman's Wharf": 25,
            "Bayview": 0
        },
        "Embarcadero": {
            "Bayview": 21,
            "Richmond District": 21,
            "Fisherman's Wharf": 6,
            "Embarcadero": 0
        },
        "Richmond District": {
            "Bayview": 26,
            "Embarcadero": 19,
            "Fisherman's Wharf": 18,
            "Richmond District": 0
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "Embarcadero": 8,
            "Richmond District": 18,
            "Fisherman's Wharf": 0
        }
    }
    
    # Times in minutes since midnight.
    # 9:00AM = 9*60 = 540
    # Jessica: 16:45 = 16*60+45 = 1005, 19:00 = 1140
    # Sandra: 18:30 = 18*60+30 = 1110, 21:45 = 1305
    # Jason: 16:00 = 960, 16:45 = 1005
    friends_data = [
        {
            "person": "Jessica",
            "location": "Embarcadero",
            "avail_start": 1005,  # 16:45
            "avail_end": 1140,    # 19:00
            "min_meeting": 30
        },
        {
            "person": "Sandra",
            "location": "Richmond District",
            "avail_start": 1110,  # 18:30
            "avail_end": 1305,    # 21:45
            "min_meeting": 120
        },
        {
            "person": "Jason",
            "location": "Fisherman's Wharf",
            "avail_start": 960,   # 16:00
            "avail_end": 1005,    # 16:45
            "min_meeting": 30
        }
    ]
    
    start_location = "Bayview"
    start_time = 540  #9:00AM
    
    best_itinerary = None
    best_finish_time = None
    best_count = 0
    
    # Try all permutations of the friends list.
    for order in itertools.permutations(friends_data):
        valid, itinerary, finish_time = compute_schedule(start_location, start_time, friends_data, travel_times, order)
        if valid:
            count = len(itinerary)
            # We want to maximize the number of meetings.
            if count > best_count:
                best_count = count
                best_itinerary = itinerary
                best_finish_time = finish_time
            elif count == best_count:
                # tie-breaker: choose one that finishes earlier
                if best_finish_time is None or finish_time < best_finish_time:
                    best_itinerary = itinerary
                    best_finish_time = finish_time

    # If no valid itinerary meeting any friend was found, plan empty itinerary.
    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()