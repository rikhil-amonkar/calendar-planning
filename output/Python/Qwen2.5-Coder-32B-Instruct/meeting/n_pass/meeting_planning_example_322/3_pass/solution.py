import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Presidio"): 17
}

# Define meeting constraints
meetings = {
    "William": {"location": "Russian Hill", "start": "18:30", "end": "20:45", "min_duration": 105},
    "Michelle": {"location": "Chinatown", "start": "8:15", "end": "14:00", "min_duration": 15},
    "George": {"location": "Presidio", "start": "10:30", "end": "18:45", "min_duration": 30},
    "Robert": {"location": "Fisherman's Wharf", "start": "9:00", "end": "13:45", "min_duration": 30}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def add_minutes(time_obj, minutes):
    return (datetime.combine(datetime.today(), time_obj) + timedelta(minutes=minutes)).time()

def can_meet(start_time, end_time, meeting_start, meeting_end, min_duration):
    meeting_start_time = parse_time(meeting_start)
    meeting_end_time = parse_time(meeting_end)
    if start_time >= meeting_start_time and end_time <= meeting_end_time:
        return (datetime.combine(datetime.today(), end_time) - datetime.combine(datetime.today(), start_time)).seconds // 60 >= min_duration
    return False

def find_optimal_schedule():
    current_time = parse_time("9:00")
    current_location = "Sunset District"
    itinerary = []

    def visit(location, start_time, end_time, person, min_duration):
        nonlocal current_time, current_location, itinerary
        travel_time = travel_times[(current_location, location)]
        arrival_time = add_minutes(current_time, travel_time)
        if arrival_time < parse_time(start_time):
            arrival_time = parse_time(start_time)
        meeting_start_time = arrival_time
        meeting_end_time = add_minutes(meeting_start_time, min_duration)
        if meeting_end_time > parse_time(end_time):
            meeting_end_time = parse_time(end_time)
        if can_meet(meeting_start_time, meeting_end_time, start_time, end_time, min_duration):
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meeting_start_time.strftime("%H:%M"),
                "end_time": meeting_end_time.strftime("%H:%M")
            })
            current_time = meeting_end_time
            current_location = location

    # Try to meet Michelle first since she leaves early
    visit("Chinatown", meetings["Michelle"]["start"], meetings["Michelle"]["end"], "Michelle", meetings["Michelle"]["min_duration"])
    
    # Try to meet Robert next since he leaves early
    visit("Fisherman's Wharf", meetings["Robert"]["start"], meetings["Robert"]["end"], "Robert", meetings["Robert"]["min_duration"])
    
    # Try to meet George next
    visit("Presidio", meetings["George"]["start"], meetings["George"]["end"], "George", meetings["George"]["min_duration"])
    
    # Finally, try to meet William
    visit("Russian Hill", meetings["William"]["start"], meetings["William"]["end"], "William", meetings["William"]["min_duration"])

    return itinerary

itinerary = find_optimal_schedule()
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))