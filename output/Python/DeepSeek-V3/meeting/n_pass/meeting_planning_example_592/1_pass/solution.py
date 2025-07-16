import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (from -> to)
travel_times = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17
    }
}

# Meeting constraints
meetings = [
    {
        "person": "James",
        "location": "Pacific Heights",
        "available_start": "20:00",
        "available_end": "22:00",
        "min_duration": 120
    },
    {
        "person": "Robert",
        "location": "Chinatown",
        "available_start": "12:15",
        "available_end": "16:45",
        "min_duration": 90
    },
    {
        "person": "Jeffrey",
        "location": "Union Square",
        "available_start": "9:30",
        "available_end": "15:30",
        "min_duration": 120
    },
    {
        "person": "Carol",
        "location": "Mission District",
        "available_start": "18:15",
        "available_end": "21:15",
        "min_duration": 15
    },
    {
        "person": "Mark",
        "location": "Golden Gate Park",
        "available_start": "11:30",
        "available_end": "17:45",
        "min_duration": 15
    },
    {
        "person": "Sandra",
        "location": "Nob Hill",
        "available_start": "8:00",
        "available_end": "15:30",
        "min_duration": 15
    }
]

def calculate_schedule():
    current_location = "North Beach"
    current_time = time_to_minutes("9:00")
    itinerary = []
    remaining_meetings = meetings.copy()
    
    # Sort meetings by earliest available start time
    remaining_meetings.sort(key=lambda x: time_to_minutes(x["available_start"]))
    
    while remaining_meetings:
        best_meeting = None
        best_start = None
        best_end = None
        best_travel_time = None
        
        for meeting in remaining_meetings:
            available_start = time_to_minutes(meeting["available_start"])
            available_end = time_to_minutes(meeting["available_end"])
            travel_time = travel_times[current_location][meeting["location"]]
            
            # Earliest possible start time is max of current_time + travel or available_start
            start_time = max(current_time + travel_time, available_start)
            end_time = start_time + meeting["min_duration"]
            
            if end_time <= available_end:
                if best_meeting is None or start_time < best_start:
                    best_meeting = meeting
                    best_start = start_time
                    best_end = end_time
                    best_travel_time = travel_time
        
        if best_meeting is None:
            break  # No more feasible meetings
        
        # Add travel if needed
        if best_travel_time > 0:
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": best_meeting["location"],
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + best_travel_time)
            })
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": best_meeting["location"],
            "person": best_meeting["person"],
            "start_time": minutes_to_time(best_start),
            "end_time": minutes_to_time(best_end)
        })
        
        # Update state
        current_location = best_meeting["location"]
        current_time = best_end
        remaining_meetings.remove(best_meeting)
    
    # Filter out travel actions and convert to required format
    result = {
        "itinerary": [
            {
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": item["start_time"],
                "end_time": item["end_time"]
            }
            for item in itinerary if item["action"] == "meet"
        ]
    }
    
    return result

# Calculate and print the schedule
schedule = calculate_schedule()
print(json.dumps(schedule, indent=2))