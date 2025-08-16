import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Embarcadero"): 31,
    ("Sunset District", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
}

# Define meeting constraints
meetings = {
    "Emily": {"location": "Russian Hill", "start": "12:15", "end": "14:15", "min_duration": 105},
    "Mark": {"location": "Presidio", "start": "14:45", "end": "19:30", "min_duration": 60},
    "Deborah": {"location": "Chinatown", "start": "07:30", "end": "15:30", "min_duration": 45},
    "Margaret": {"location": "Sunset District", "start": "21:30", "end": "22:30", "min_duration": 60},
    "George": {"location": "The Castro", "start": "07:30", "end": "14:15", "min_duration": 60},
    "Andrew": {"location": "Embarcadero", "start": "20:15", "end": "22:00", "min_duration": 75},
    "Steven": {"location": "Golden Gate Park", "start": "11:15", "end": "21:15", "min_duration": 105},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Calculate the duration between two datetime objects
def duration(start, end):
    return (end - start).total_seconds() / 60

# Check if a meeting can fit within the available time
def can_meet(start, end, min_duration):
    return duration(start, end) >= min_duration

# Find the best meeting time within the person's availability
def find_best_meeting_time(current_time, person_info):
    start = parse_time(person_info["start"])
    end = parse_time(person_info["end"])
    min_duration = person_info["min_duration"]
    
    # If the current time is before the person's start time, wait until they arrive
    if current_time < start:
        current_time = start
    
    # Calculate the latest possible start time to meet the minimum duration requirement
    latest_start = end - timedelta(minutes=min_duration)
    
    # If the current time is after the latest possible start time, it's too late to meet
    if current_time > latest_start:
        return None
    
    # Return the meeting start and end times
    meeting_start = max(current_time, start)
    meeting_end = meeting_start + timedelta(minutes=min_duration)
    return meeting_start, meeting_end

# Main function to calculate the optimal meeting schedule
def calculate_schedule():
    itinerary = []
    current_location = "Alamo Square"
    current_time = parse_time("09:00")
    
    # Sort meetings by their earliest start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]["start"]))
    
    for name, person_info in sorted_meetings:
        location = person_info["location"]
        
        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]
        current_time += timedelta(minutes=travel_time)
        
        # Find the best meeting time within the person's availability
        meeting_times = find_best_meeting_time(current_time, person_info)
        
        if meeting_times:
            meeting_start, meeting_end = meeting_times
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            })
            
            # Update current time and location
            current_time = meeting_end
            current_location = location
    
    return itinerary

# Generate the final schedule
schedule = calculate_schedule()

# Output the schedule as JSON
print(json.dumps({"itinerary": schedule}, indent=2))