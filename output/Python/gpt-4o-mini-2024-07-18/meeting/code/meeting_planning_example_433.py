import json
from datetime import datetime, timedelta

# Travel times between locations (in minutes)
travel_times = {
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

# Meeting constraints
meetings = [
    {"person": "Emily", "location": "Richmond District", "min_duration": 15, "available_from": "19:00", "available_to": "21:00"},
    {"person": "Margaret", "location": "Financial District", "min_duration": 75, "available_from": "16:30", "available_to": "20:15"},
    {"person": "Ronald", "location": "North Beach", "min_duration": 45, "available_from": "18:30", "available_to": "19:30"},
    {"person": "Deborah", "location": "The Castro", "min_duration": 90, "available_from": "13:45", "available_to": "21:15"},
    {"person": "Jeffrey", "location": "Golden Gate Park", "min_duration": 120, "available_from": "11:15", "available_to": "14:30"},
]

# Start time at Nob Hill
start_time = datetime.strptime("09:00", "%H:%M")

# Store the final itinerary
itinerary = []

# Function to schedule meetings
def schedule_meetings(itinerary, start_time, meetings):
    current_time = start_time
    for meeting in meetings:
        available_from = datetime.strptime(meeting['available_from'], "%H:%M")
        available_to = datetime.strptime(meeting['available_to'], "%H:%M")
        duration = timedelta(minutes=meeting['min_duration'])
        
        # Calculate the travel time to the meeting location
        travel_time = travel_times.get(("Nob Hill", meeting['location']), 0)
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we can meet this person
        if arrival_time < available_from:
            arrival_time = available_from
        
        meeting_end_time = arrival_time + duration
        travel_back_time = travel_times.get((meeting['location'], "Nob Hill"), 0)
        
        # Check if the meeting can fit into the available window
        if meeting_end_time <= available_to and arrival_time < available_to:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": arrival_time.strftime("%H:%M"),
                "end_time": meeting_end_time.strftime("%H:%M")
            })
            # Update current time after returning to Nob Hill
            current_time = meeting_end_time + timedelta(minutes=travel_back_time)

# Schedule the meetings
schedule_meetings(itinerary, start_time, meetings)

# Output the itinerary in JSON format
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))