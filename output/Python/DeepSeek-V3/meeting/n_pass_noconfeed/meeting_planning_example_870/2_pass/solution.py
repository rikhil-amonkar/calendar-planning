import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define travel times as a dictionary of dictionaries
travel_times = {
    "Pacific Heights": {
        "Marina District": 6,
        "The Castro": 16,
        "Richmond District": 12,
        "Alamo Square": 10,
        "Financial District": 13,
        "Presidio": 11,
        "Mission District": 15,
        "Nob Hill": 8,
        "Russian Hill": 7
    },
    "Marina District": {
        "Pacific Heights": 7,
        "The Castro": 22,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Presidio": 10,
        "Mission District": 20,
        "Nob Hill": 12,
        "Russian Hill": 8
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Presidio": 20,
        "Mission District": 7,
        "Nob Hill": 16,
        "Russian Hill": 18
    },
    "Richmond District": {
        "Pacific Heights": 10,
        "Marina District": 9,
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Presidio": 7,
        "Mission District": 20,
        "Nob Hill": 17,
        "Russian Hill": 13
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Marina District": 15,
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Presidio": 17,
        "Mission District": 10,
        "Nob Hill": 11,
        "Russian Hill": 13
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Marina District": 15,
        "The Castro": 20,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Presidio": 22,
        "Mission District": 17,
        "Nob Hill": 8,
        "Russian Hill": 11
    },
    "Presidio": {
        "Pacific Heights": 11,
        "Marina District": 11,
        "The Castro": 21,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Mission District": 26,
        "Nob Hill": 18,
        "Russian Hill": 14
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Marina District": 19,
        "The Castro": 7,
        "Richmond District": 20,
        "Alamo Square": 11,
        "Financial District": 15,
        "Presidio": 25,
        "Nob Hill": 12,
        "Russian Hill": 15
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Marina District": 11,
        "The Castro": 17,
        "Richmond District": 14,
        "Alamo Square": 11,
        "Financial District": 9,
        "Presidio": 17,
        "Mission District": 13,
        "Russian Hill": 5
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Marina District": 7,
        "The Castro": 21,
        "Richmond District": 14,
        "Alamo Square": 15,
        "Financial District": 11,
        "Presidio": 14,
        "Mission District": 16,
        "Nob Hill": 5
    }
}

# Define meeting constraints
meetings = [
    {"person": "Linda", "location": "Marina District", "start": "18:00", "end": "22:00", "duration": 30},
    {"person": "Kenneth", "location": "The Castro", "start": "14:45", "end": "16:15", "duration": 30},
    {"person": "Kimberly", "location": "Richmond District", "start": "14:15", "end": "22:00", "duration": 30},
    {"person": "Paul", "location": "Alamo Square", "start": "21:00", "end": "21:30", "duration": 15},
    {"person": "Carol", "location": "Financial District", "start": "10:15", "end": "12:00", "duration": 60},
    {"person": "Brian", "location": "Presidio", "start": "10:00", "end": "21:30", "duration": 75},
    {"person": "Laura", "location": "Mission District", "start": "16:15", "end": "20:30", "duration": 30},
    {"person": "Sandra", "location": "Nob Hill", "start": "9:15", "end": "18:30", "duration": 60},
    {"person": "Karen", "location": "Russian Hill", "start": "18:30", "end": "22:00", "duration": 75}
]

def generate_schedule():
    current_time = time_to_minutes("9:00")
    current_location = "Pacific Heights"
    schedule = []
    scheduled_meetings = set()
    
    # Sort meetings by urgency (earliest end time first)
    sorted_meetings = sorted(meetings, key=lambda m: time_to_minutes(m["end"]))
    
    while len(scheduled_meetings) < len(meetings):
        best_meeting = None
        best_start_time = None
        best_travel_time = None
        
        for meeting in sorted_meetings:
            if meeting["person"] in scheduled_meetings:
                continue
                
            location = meeting["location"]
            travel_time = travel_times[current_location][location]
            arrival_time = current_time + travel_time
            
            meeting_start = time_to_minutes(meeting["start"])
            meeting_end = time_to_minutes(meeting["end"])
            duration = meeting["duration"]
            
            # Calculate possible start time
            start_time = max(arrival_time, meeting_start)
            if start_time + duration > meeting_end:
                continue  # Can't schedule this meeting
                
            # Check if this is better than current best
            if best_meeting is None or start_time < best_start_time:
                best_meeting = meeting
                best_start_time = start_time
                best_travel_time = travel_time
        
        if best_meeting is None:
            break  # No more meetings can be scheduled
            
        # Schedule the best meeting
        end_time = best_start_time + best_meeting["duration"]
        schedule.append({
            "action": "meet",
            "location": best_meeting["location"],
            "person": best_meeting["person"],
            "start_time": minutes_to_time(best_start_time),
            "end_time": minutes_to_time(end_time),
            "travel_time": best_travel_time
        })
        
        scheduled_meetings.add(best_meeting["person"])
        current_time = end_time
        current_location = best_meeting["location"]
    
    return schedule

def main():
    schedule = generate_schedule()
    
    if schedule:
        output = {"itinerary": schedule}
    else:
        output = {"itinerary": []}
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()