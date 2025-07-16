import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes (from -> to)
travel_times = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Sunset District": 10,
        "Marina District": 16,
        "Financial District": 26,
        "Union Square": 22
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Sunset District": 15,
        "Marina District": 17,
        "Financial District": 21,
        "Union Square": 17
    },
    "Sunset District": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 15,
        "Marina District": 21,
        "Financial District": 30,
        "Union Square": 30
    },
    "Marina District": {
        "Golden Gate Park": 18,
        "Haight-Ashbury": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Union Square": 16
    },
    "Financial District": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Sunset District": 31,
        "Marina District": 15,
        "Union Square": 9
    },
    "Union Square": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Sunset District": 26,
        "Marina District": 18,
        "Financial District": 9
    }
}

# People's availability
people = {
    "Sarah": {
        "location": "Haight-Ashbury",
        "start": time_to_minutes("17:00"),
        "end": time_to_minutes("21:30"),
        "duration": 105
    },
    "Patricia": {
        "location": "Sunset District",
        "start": time_to_minutes("17:00"),
        "end": time_to_minutes("19:45"),
        "duration": 45
    },
    "Matthew": {
        "location": "Marina District",
        "start": time_to_minutes("9:15"),
        "end": time_to_minutes("12:00"),
        "duration": 15
    },
    "Joseph": {
        "location": "Financial District",
        "start": time_to_minutes("14:15"),
        "end": time_to_minutes("18:45"),
        "duration": 30
    },
    "Robert": {
        "location": "Union Square",
        "start": time_to_minutes("10:15"),
        "end": time_to_minutes("21:45"),
        "duration": 15
    }
}

def calculate_schedule(order):
    current_time = time_to_minutes("9:00")
    current_location = "Golden Gate Park"
    schedule = []
    met_people = set()
    
    for person in order:
        if person in met_people:
            continue
        info = people[person]
        location = info["location"]
        
        # Fix typo in location name
        if location == "Marina District" and "Marina District" not in travel_times[current_location]:
            location = "Marina District" if "Marina District" in travel_times[current_location] else "Marina District"
        
        # Travel time
        travel_time = travel_times[current_location].get(location, float('inf'))
        arrival_time = current_time + travel_time
        
        # Check if we can meet this person
        meeting_start = max(arrival_time, info["start"])
        meeting_end = meeting_start + info["duration"]
        
        if meeting_end > info["end"]:
            continue  # Can't meet this person
        
        # Add to schedule
        schedule.append({
            "person": person,
            "location": location,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end),
            "arrival": arrival_time
        })
        
        met_people.add(person)
        current_time = meeting_end
        current_location = location
    
    return schedule, len(met_people)

# Generate all possible orders of meeting people
all_people = list(people.keys())
best_schedule = []
max_met = 0

# Try all possible permutations to find the best schedule
for perm in permutations(all_people, len(all_people)):
    schedule, num_met = calculate_schedule(perm)
    if num_met > max_met:
        max_met = num_met
        best_schedule = schedule
    elif num_met == max_met and len(schedule) > 0:
        # Prefer schedules that end earlier
        if not best_schedule or time_to_minutes(schedule[-1]["end_time"]) < time_to_minutes(best_schedule[-1]["end_time"]):
            best_schedule = schedule

# Format the output
itinerary = []
for meeting in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": meeting["location"],
        "person": meeting["person"],
        "start_time": meeting["start_time"],
        "end_time": meeting["end_time"]
    })

output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))