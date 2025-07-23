from z3 import *

# Define the locations and their travel times
locations = [
    "Union Square", "Mission District", "Fisherman's Wharf", "Russian Hill",
    "Marina District", "North Beach", "Chinatown", "Pacific Heights",
    "The Castro", "Nob Hill", "Sunset District"
]

travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Sunset District"): 24,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Sunset District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Sunset District"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 24,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Nob Hill"): 27,
}

# Define the meetings and their constraints
meetings = {
    "Kevin": {"location": "Mission District", "start": 2045, "end": 2145, "duration": 60},
    "Mark": {"location": "Fisherman's Wharf", "start": 1715, "end": 2000, "duration": 90},
    "Jessica": {"location": "Russian Hill", "start": 900, "end": 1500, "duration": 120},
    "Jason": {"location": "Marina District", "start": 1515, "end": 2145, "duration": 120},
    "John": {"location": "North Beach", "start": 945, "end": 1800, "duration": 15},
    "Karen": {"location": "Chinatown", "start": 1645, "end": 1900, "duration": 75},
    "Sarah": {"location": "Pacific Heights", "start": 1730, "end": 1815, "duration": 45},
    "Amanda": {"location": "The Castro", "start": 2000, "end": 2115, "duration": 60},
    "Nancy": {"location": "Nob Hill", "start": 945, "end": 1300, "duration": 45},
    "Rebecca": {"location": "Sunset District", "start": 845, "end": 1500, "duration": 75},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Greedy algorithm to find a feasible itinerary
def find_feasible_itinerary(meetings, travel_times):
    current_time = time_to_minutes(900)  # 9:00 AM
    current_location = "Union Square"
    itinerary = []

    # Sort meetings by their start times
    sorted_meetings = sorted(meetings.items(), key=lambda x: x[1]["start"])

    for name, details in sorted_meetings:
        location = details["location"]
        start = time_to_minutes(details["start"])
        end = time_to_minutes(details["end"])
        duration = details["duration"]
        travel_time = travel_times[(current_location, location)]

        # Check if we can fit the meeting
        if current_time + travel_time + duration <= end:
            current_time += travel_time
            meeting_start = current_time
            meeting_end = meeting_start + duration
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{meeting_start // 60:02}:{meeting_start % 60:02}",
                "end_time": f"{meeting_end // 60:02}:{meeting_end % 60:02}"
            })
            current_time = meeting_end
            current_location = location

    return itinerary

itinerary = find_feasible_itinerary(meetings, travel_times)
if itinerary:
    print({"itinerary": itinerary})
else:
    print("No solution found")