#!/usr/bin/env python3
import json

def format_time(total_minutes):
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

# Travel time data as provided.
# Keys: origin, inner dictionary: destination -> travel time in minutes.
travel_times = {
    "The Castro": {
        "Marina District": 21,
        "Presidio": 20,
        "North Beach": 20,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Sunset District": 17
    },
    "Marina District": {
        "The Castro": 22,
        "Presidio": 10,
        "North Beach": 11,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Sunset District": 19
    },
    "Presidio": {
        "The Castro": 21,
        "Marina District": 11,
        "North Beach": 18,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Sunset District": 15
    },
    "North Beach": {
        "The Castro": 23,
        "Marina District": 9,
        "Presidio": 17,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Alamo Square": 16,
        "Financial District": 8,
        "Sunset District": 27
    },
    "Embarcadero": {
        "The Castro": 25,
        "Marina District": 12,
        "Presidio": 20,
        "North Beach": 5,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Alamo Square": 19,
        "Financial District": 5,
        "Sunset District": 30
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Marina District": 17,
        "Presidio": 15,
        "North Beach": 19,
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Richmond District": 10,
        "Alamo Square": 5,
        "Financial District": 21,
        "Sunset District": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Marina District": 16,
        "Presidio": 11,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Alamo Square": 9,
        "Financial District": 26,
        "Sunset District": 10
    },
    "Richmond District": {
        "The Castro": 16,
        "Marina District": 9,
        "Presidio": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Golden Gate Park": 9,
        "Alamo Square": 13,
        "Financial District": 22,
        "Sunset District": 11
    },
    "Alamo Square": {
        "The Castro": 8,
        "Marina District": 15,
        "Presidio": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Financial District": 17,
        "Sunset District": 16
    },
    "Financial District": {
        "The Castro": 20,
        "Marina District": 15,
        "Presidio": 22,
        "North Beach": 7,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Sunset District": 30
    },
    "Sunset District": {
        "The Castro": 17,
        "Marina District": 21,
        "Presidio": 16,
        "North Beach": 28,
        "Embarcadero": 30,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Richmond District": 12,
        "Alamo Square": 17,
        "Financial District": 30
    }
}

# Evening meeting candidate information.
# Times are represented in minutes from midnight.
# Available window: window_start to window_end, meeting duration is the minimum required.
evening_meetings = [
    {
        "person": "Helen",
        "location": "Financial District",
        "window_start": 17*60 + 30,  # 17:30 -> 1050
        "window_end": 18*60 + 30,    # 18:30 -> 1110
        "duration": 45
    },
    {
        "person": "Kimberly",
        "location": "Haight-Ashbury",
        "window_start": 16*60 + 45,  # 16:45 -> 1005
        "window_end": 21*60 + 30,    # 21:30 -> 1290
        "duration": 75
    },
    {
        "person": "Lisa",
        "location": "Golden Gate Park",
        "window_start": 17*60 + 30,  # 17:30 -> 1050
        "window_end": 21*60 + 45,    # 21:45 -> 1305
        "duration": 45
    },
    {
        "person": "Elizabeth",
        "location": "Marina District",
        "window_start": 19*60,       # 19:00 -> 1140
        "window_end": 20*60 + 45,      # 20:45 -> 1245
        "duration": 105
    },
    {
        "person": "Timothy",
        "location": "North Beach",
        "window_start": 19*60 + 45,   # 19:45 -> 1185
        "window_end": 22*60,         # 22:00 -> 1320
        "duration": 90
    },
    {
        "person": "Laura",
        "location": "Sunset District",
        "window_start": 17*60 + 45,   # 17:45 -> 1065
        "window_end": 21*60 + 15,      # 21:15 -> 1275
        "duration": 90
    }
]

# Backtracking search to choose the optimal (maximum count) sequence of evening meetings.
# State: current_time (in minutes), current_location, available meetings list.
def search_evening(current_time, current_location, available):
    best_schedule = []
    best_count = 0
    for i, meeting in enumerate(available):
        # Compute travel time from current location to candidate meeting location.
        travel = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel
        # The meeting can only start when the friend is available.
        meeting_start = max(arrival_time, meeting["window_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Check if meeting can finish within the friend's availability window.
        if meeting_end <= meeting["window_end"]:
            # Create an event record (times in minutes).
            event = {
                "person": meeting["person"],
                "location": meeting["location"],
                "start": meeting_start,
                "end": meeting_end
            }
            # Exclude this meeting from the remaining list.
            remaining = available[:i] + available[i+1:]
            sub_count, sub_schedule = search_evening(meeting_end, meeting["location"], remaining)
            total_count = 1 + sub_count
            if total_count > best_count:
                best_count = total_count
                best_schedule = [event] + sub_schedule
    return best_count, best_schedule

def main():
    itinerary = []
    
    # Fixed morning/afternoon schedule.
    # You arrive at The Castro at 9:00 (9*60 = 540).
    # 1. Joshua at Presidio.
    start_castro = 9 * 60  # 540 minutes
    # Travel from The Castro to Presidio: 20 minutes.
    joshua_start = start_castro + travel_times["The Castro"]["Presidio"]  # 540 + 20 = 560 (9:20)
    joshua_end = joshua_start + 105  # 105 minutes meeting => 560 + 105 = 665 (11:05)
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Joshua",
        "start_time": format_time(joshua_start),
        "end_time": format_time(joshua_end)
    })
    
    # 2. David at Embarcadero.
    # Travel from Presidio to Embarcadero: 20 minutes.
    david_arrival = joshua_end + travel_times["Presidio"]["Embarcadero"]  # 665 + 20 = 685 (11:25)
    david_meeting_duration = 30  # minimum 30 minutes
    david_end = david_arrival + david_meeting_duration  # 685 + 30 = 715 (11:55)
    itinerary.append({
        "action": "meet",
        "location": "Embarcadero",
        "person": "David",
        "start_time": format_time(david_arrival),
        "end_time": format_time(david_end)
    })
    
    # 3. Stephanie at Alamo Square.
    # Travel from Embarcadero to Alamo Square: 19 minutes.
    stephanie_arrival = david_end + travel_times["Embarcadero"]["Alamo Square"]  # 715 + 19 = 734
    # However, Stephanie is available from 15:30 (930 minutes) to 16:30.
    # We wait until her window opens.
    stephanie_start = max(stephanie_arrival, 15*60 + 30)  # 15:30 = 930
    stephanie_duration = 30
    stephanie_end = stephanie_start + stephanie_duration  # 930 + 30 = 960 (16:00)
    itinerary.append({
        "action": "meet",
        "location": "Alamo Square",
        "person": "Stephanie",
        "start_time": format_time(stephanie_start),
        "end_time": format_time(stephanie_end)
    })
    
    # Evening scheduling.
    # Start state: location = "Alamo Square", time = end of Stephanie meeting = 960 (16:00)
    evening_start_time = stephanie_end  # 960 minutes (16:00)
    current_location = "Alamo Square"
    
    # Compute the optimal sequence using backtracking.
    _, evening_schedule = search_evening(evening_start_time, current_location, evening_meetings)
    
    # Append the evening events (convert times to strings)
    for event in evening_schedule:
        itinerary.append({
            "action": "meet",
            "location": event["location"],
            "person": event["person"],
            "start_time": format_time(event["start"]),
            "end_time": format_time(event["end"])
        })
    
    # Prepare final result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()