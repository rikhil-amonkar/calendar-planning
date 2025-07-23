import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Haight-Ashbury"): 18,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Haight-Ashbury"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Haight-Ashbury"): 18,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
}

# Define meeting constraints
meetings = {
    "Melissa": {"location": "The Castro", "start": "20:15", "end": "21:15", "min_duration": 30},
    "Kimberly": {"location": "North Beach", "start": "07:00", "end": "10:30", "min_duration": 15},
    "Joseph": {"location": "Embarcadero", "start": "15:30", "end": "19:30", "min_duration": 75},
    "Barbara": {"location": "Alamo Square", "start": "20:45", "end": "21:45", "min_duration": 15},
    "Kenneth": {"location": "Nob Hill", "start": "12:15", "end": "17:15", "min_duration": 105},
    "Joshua": {"location": "Presidio", "start": "16:30", "end": "18:15", "min_duration": 105},
    "Brian": {"location": "Fisherman's Wharf", "start": "09:30", "end": "15:30", "min_duration": 45},
    "Steven": {"location": "Mission District", "start": "19:30", "end": "21:00", "min_duration": 90},
    "Betty": {"location": "Haight-Ashbury", "start": "19:00", "end": "20:30", "min_duration": 90},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def find_optimal_schedule(start_time, meetings, travel_times):
    def can_meet(meeting, current_time):
        meeting_start = parse_time(meeting["start"])
        meeting_end = parse_time(meeting["end"])
        return meeting_start <= current_time <= meeting_end - timedelta(minutes=meeting["min_duration"])

    def next_location(current_location, current_time, remaining_meetings):
        best_schedule = None
        best_time = timedelta(hours=23, minutes=59)

        for person, meeting in remaining_meetings.items():
            location = meeting["location"]
            if can_meet(meeting, current_time):
                travel_time = travel_times.get((current_location, location), float('inf'))
                new_time = current_time + timedelta(minutes=travel_time)
                if new_time + timedelta(minutes=meeting["min_duration"]) <= parse_time(meeting["end"]):
                    schedule = [{"action": "travel", "location": location, "start_time": time_to_str(current_time), "end_time": time_to_str(new_time)}]
                    schedule.append({"action": "meet", "location": location, "person": person, "start_time": time_to_str(new_time), "end_time": time_to_str(new_time + timedelta(minutes=meeting["min_duration"]))})
                    remaining = remaining_meetings.copy()
                    del remaining[person]
                    next_sched, next_time = next_location(location, new_time + timedelta(minutes=meeting["min_duration"]), remaining)
                    if next_sched is not None:
                        schedule.extend(next_sched)
                        total_time = next_time - current_time
                        if total_time < best_time:
                            best_schedule = schedule
                            best_time = total_time
        return best_schedule, best_time

    start_location = "Union Square"
    itinerary, _ = next_location(start_location, parse_time(start_time), meetings)
    return itinerary

start_time = "09:00"
optimal_itinerary = find_optimal_schedule(start_time, meetings, travel_times)

# Format the output as JSON
output = {
    "itinerary": optimal_itinerary
}

print(json.dumps(output))