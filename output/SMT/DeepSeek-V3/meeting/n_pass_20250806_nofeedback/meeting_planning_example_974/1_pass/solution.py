from z3 import *
import json

# Define the travel times between districts
travel_times = {
    "Sunset District": {
        "Presidio": 16,
        "Nob Hill": 27,
        "Pacific Heights": 21,
        "Mission District": 25,
        "Marina District": 21,
        "North Beach": 28,
        "Russian Hill": 24,
        "Richmond District": 12,
        "Embarcadero": 30,
        "Alamo Square": 17
    },
    "Presidio": {
        "Sunset District": 15,
        "Nob Hill": 18,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Marina District": 11,
        "North Beach": 18,
        "Russian Hill": 14,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Alamo Square": 19
    },
    "Nob Hill": {
        "Sunset District": 24,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Mission District": 13,
        "Marina District": 11,
        "North Beach": 8,
        "Russian Hill": 5,
        "Richmond District": 14,
        "Embarcadero": 9,
        "Alamo Square": 11
    },
    "Pacific Heights": {
        "Sunset District": 21,
        "Presidio": 11,
        "Nob Hill": 8,
        "Mission District": 15,
        "Marina District": 6,
        "North Beach": 9,
        "Russian Hill": 7,
        "Richmond District": 12,
        "Embarcadero": 10,
        "Alamo Square": 10
    },
    "Mission District": {
        "Sunset District": 24,
        "Presidio": 25,
        "Nob Hill": 12,
        "Pacific Heights": 16,
        "Marina District": 19,
        "North Beach": 17,
        "Russian Hill": 15,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Alamo Square": 11
    },
    "Marina District": {
        "Sunset District": 19,
        "Presidio": 10,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Mission District": 20,
        "North Beach": 11,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Alamo Square": 15
    },
    "North Beach": {
        "Sunset District": 27,
        "Presidio": 17,
        "Nob Hill": 7,
        "Pacific Heights": 8,
        "Mission District": 18,
        "Marina District": 9,
        "Russian Hill": 4,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Alamo Square": 16
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Presidio": 14,
        "Nob Hill": 5,
        "Pacific Heights": 7,
        "Mission District": 16,
        "Marina District": 7,
        "North Beach": 5,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Alamo Square": 15
    },
    "Richmond District": {
        "Sunset District": 11,
        "Presidio": 7,
        "Nob Hill": 17,
        "Pacific Heights": 10,
        "Mission District": 20,
        "Marina District": 9,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19,
        "Alamo Square": 13
    },
    "Embarcadero": {
        "Sunset District": 30,
        "Presidio": 20,
        "Nob Hill": 10,
        "Pacific Heights": 11,
        "Mission District": 20,
        "Marina District": 12,
        "North Beach": 5,
        "Russian Hill": 8,
        "Richmond District": 21,
        "Alamo Square": 19
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Presidio": 17,
        "Nob Hill": 11,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Marina District": 15,
        "North Beach": 15,
        "Russian Hill": 13,
        "Richmond District": 11,
        "Embarcadero": 16
    }
}

# Define the friends and their constraints
friends = [
    {"name": "Charles", "location": "Presidio", "available_start": "13:15", "available_end": "15:00", "duration": 105},
    {"name": "Robert", "location": "Nob Hill", "available_start": "13:15", "available_end": "17:30", "duration": 90},
    {"name": "Nancy", "location": "Pacific Heights", "available_start": "14:45", "available_end": "22:00", "duration": 105},
    {"name": "Brian", "location": "Mission District", "available_start": "15:30", "available_end": "22:00", "duration": 60},
    {"name": "Kimberly", "location": "Marina District", "available_start": "17:00", "available_end": "19:45", "duration": 75},
    {"name": "David", "location": "North Beach", "available_start": "14:45", "available_end": "16:30", "duration": 75},
    {"name": "William", "location": "Russian Hill", "available_start": "12:30", "available_end": "19:15", "duration": 120},
    {"name": "Jeffrey", "location": "Richmond District", "available_start": "12:00", "available_end": "19:15", "duration": 45},
    {"name": "Karen", "location": "Embarcadero", "available_start": "14:15", "available_end": "20:45", "duration": 60},
    {"name": "Joshua", "location": "Alamo Square", "available_start": "18:45", "available_end": "22:00", "duration": 60}
]

# Convert time strings to minutes since 9:00 AM (540 minutes)
def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm - 540  # Subtract 540 to start from 9:00 AM (540 minutes)

# Convert minutes back to time string
def minutes_to_time(minutes):
    total_minutes = minutes + 540
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Initialize Z3 solver
s = Solver()

# Create variables for each friend's start and end times
meetings = []
for friend in friends:
    start = Int(f"start_{friend['name']}")
    end = Int(f"end_{friend['name']}")
    duration = friend['duration']
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    s.add(start >= available_start)
    s.add(end <= available_end)
    s.add(end == start + duration)
    meetings.append({
        "name": friend['name'],
        "location": friend['location'],
        "start": start,
        "end": end
    })

# Add constraints for travel times
for i in range(len(meetings)):
    for j in range(len(meetings)):
        if i != j:
            # Ensure no overlap or travel time violation
            loc1 = meetings[i]['location']
            loc2 = meetings[j]['location']
            travel_time = travel_times[loc1][loc2]
            s.add(Or(
                meetings[j]['start'] >= meetings[i]['end'] + travel_time,
                meetings[i]['start'] >= meetings[j]['end'] + travel_time
            ))

# Add constraint for starting at Sunset District at 9:00 AM
first_meeting_start = Int("first_meeting_start")
s.add(first_meeting_start >= travel_times["Sunset District"][meetings[0]['location'])

# Try to maximize the number of friends met
# We'll prioritize meeting all friends, but if not possible, we'll relax constraints
if s.check() == sat:
    model = s.model()
    itinerary = []
    for meeting in meetings:
        start_time = model[meeting['start']].as_long()
        end_time = model[meeting['end']].as_long()
        itinerary.append({
            "action": "meet",
            "person": meeting['name'],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")