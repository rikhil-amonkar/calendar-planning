import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Union Square": 16, "Chinatown": 15,
        "Sunset District": 19, "Golden Gate Park": 18, "Financial District": 17, "Haight-Ashbury": 16, "Mission District": 20
    },
    "Embarcadero": {
        "Marina District": 12, "Bayview": 21, "Union Square": 10, "Chinatown": 7,
        "Sunset District": 30, "Golden Gate Park": 25, "Financial District": 5, "Haight-Ashbury": 21, "Mission District": 20
    },
    "Bayview": {
        "Marina District": 27, "Embarcadero": 19, "Union Square": 18, "Chinatown": 19,
        "Sunset District": 23, "Golden Gate Park": 22, "Financial District": 19, "Haight-Ashbury": 19, "Mission District": 13
    },
    "Union Square": {
        "Marina District": 18, "Embarcadero": 11, "Bayview": 15, "Chinatown": 7,
        "Sunset District": 27, "Golden Gate Park": 22, "Financial District": 9, "Haight-Ashbury": 18, "Mission District": 14
    },
    "Chinatown": {
        "Marina District": 12, "Embarcadero": 5, "Bayview": 20, "Union Square": 7,
        "Sunset District": 29, "Golden Gate Park": 23, "Financial District": 5, "Haight-Ashbury": 19, "Mission District": 17
    },
    "Sunset District": {
        "Marina District": 21, "Embarcadero": 30, "Bayview": 22, "Union Square": 30, "Chinatown": 30,
        "Golden Gate Park": 11, "Financial District": 30, "Haight-Ashbury": 15, "Mission District": 25
    },
    "Golden Gate Park": {
        "Marina District": 16, "Embarcadero": 25, "Bayview": 23, "Union Square": 22, "Chinatown": 23,
        "Sunset District": 10, "Financial District": 26, "Haight-Ashbury": 7, "Mission District": 17
    },
    "Financial District": {
        "Marina District": 15, "Embarcadero": 4, "Bayview": 19, "Union Square": 9, "Chinatown": 5,
        "Sunset District": 30, "Golden Gate Park": 23, "Haight-Ashbury": 19, "Mission District": 17
    },
    "Haight-Ashbury": {
        "Marina District": 17, "Embarcadero": 20, "Bayview": 18, "Union Square": 19, "Chinatown": 19,
        "Sunset District": 15, "Golden Gate Park": 7, "Financial District": 21, "Mission District": 11
    },
    "Mission District": {
        "Marina District": 19, "Embarcadero": 19, "Bayview": 14, "Union Square": 15, "Chinatown": 16,
        "Sunset District": 24, "Golden Gate Park": 17, "Financial District": 15, "Haight-Ashbury": 12
    }
}

# Define meeting constraints
constraints = {
    "Joshua": {"location": "Embarcadero", "start": "9:45", "end": "18:00", "min_duration": 105},
    "Jeffrey": {"location": "Bayview", "start": "9:45", "end": "20:15", "min_duration": 75},
    "Charles": {"location": "Union Square", "start": "10:45", "end": "20:15", "min_duration": 120},
    "Joseph": {"location": "Chinatown", "start": "7:00", "end": "15:30", "min_duration": 60},
    "Elizabeth": {"location": "Sunset District", "start": "9:00", "end": "9:45", "min_duration": 45},
    "Matthew": {"location": "Golden Gate Park", "start": "11:00", "end": "19:30", "min_duration": 45},
    "Carol": {"location": "Financial District", "start": "10:45", "end": "11:15", "min_duration": 15},
    "Paul": {"location": "Haight-Ashbury", "start": "19:15", "end": "20:30", "min_duration": 15},
    "Rebecca": {"location": "Mission District", "start": "17:00", "end": "21:45", "min_duration": 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def add_minutes_to_time(time, minutes):
    return (time + timedelta(minutes=minutes)).strftime("%H:%M")

def can_meet(start, end, duration):
    start_time = parse_time(start)
    end_time = parse_time(end)
    return (end_time - start_time).total_seconds() / 60 >= duration

def find_schedule():
    start_time = parse_time("9:00")
    current_location = "Marina District"
    itinerary = []

    def visit(person, start, end, min_duration):
        nonlocal start_time, current_location, itinerary
        location = constraints[person]["location"]
        travel_time = travel_times[current_location][location]
        arrival_time = add_minutes_to_time(start_time, travel_time)
        if parse_time(arrival_time) < parse_time(start):
            arrival_time = start
        meeting_start_time = arrival_time
        meeting_end_time = add_minutes_to_time(meeting_start_time, min_duration)
        if can_meet(meeting_start_time, end, min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start_time,
                "end_time": meeting_end_time
            })
            start_time = parse_time(meeting_end_time)
            current_location = location

    # Prioritize meetings based on constraints
    visit("Joseph", "7:00", "15:30", 60)
    visit("Elizabeth", "9:00", "9:45", 45)
    visit("Carol", "10:45", "11:15", 15)
    visit("Joshua", "9:45", "18:00", 105)
    visit("Matthew", "11:00", "19:30", 45)
    visit("Charles", "10:45", "20:15", 120)
    visit("Jeffrey", "9:45", "20:15", 75)
    visit("Rebecca", "17:00", "21:45", 45)
    visit("Paul", "19:15", "20:30", 15)

    return itinerary

itinerary = find_schedule()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=4))