from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Friends data: name -> {location, start_time, end_time, min_duration}
    friends = {
        "William": {"location": "Alamo Square", "start": "15:15", "end": "17:15", "duration": 60},
        "Joshua": {"location": "Richmond District", "start": "7:00", "end": "20:00", "duration": 15},
        "Joseph": {"location": "Financial District", "start": "11:15", "end": "13:30", "duration": 15},
        "David": {"location": "Union Square", "start": "16:45", "end": "19:15", "duration": 45},
        "Brian": {"location": "Fisherman's Wharf", "start": "13:45", "end": "20:45", "duration": 105},
        "Karen": {"location": "Marina District", "start": "11:30", "end": "18:30", "duration": 15},
        "Anthony": {"location": "Haight-Ashbury", "start": "7:15", "end": "10:30", "duration": 30},
        "Matthew": {"location": "Mission District", "start": "17:15", "end": "19:15", "duration": 120},
        "Helen": {"location": "Pacific Heights", "start": "8:00", "end": "12:00", "duration": 75},
        "Jeffrey": {"location": "Golden Gate Park", "start": "19:00", "end": "21:30", "duration": 60}
    }

    # Travel times between locations (in minutes)
    travel_times = {
        "The Castro": {
            "Alamo Square": 8, "Richmond District": 16, "Financial District": 21,
            "Union Square": 19, "Fisherman's Wharf": 24, "Marina District": 21,
            "Haight-Ashbury": 6, "Mission District": 7, "Pacific Heights": 16,
            "Golden Gate Park": 11
        },
        "Alamo Square": {
            "The Castro": 8, "Richmond District": 11, "Financial District": 17,
            "Union Square": 14, "Fisherman's Wharf": 19, "Marina District": 15,
            "Haight-Ashbury": 5, "Mission District": 10, "Pacific Heights": 10,
            "Golden Gate Park": 9
        },
        # ... (other locations similarly defined)
    }

    # Helper functions to convert between time strings and minutes
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting's start and end times
    meeting_starts = {name: Int(f"start_{name}") for name in friends}
    meeting_ends = {name: Int(f"end_{name}") for name in friends}

    # Add constraints for each friend's availability and duration
    for name, info in friends.items():
        start_min = time_to_minutes(info["start"])
        end_min = time_to_minutes(info["end"])
        duration = info["duration"]

        s.add(meeting_starts[name] >= start_min)
        s.add(meeting_ends[name] <= end_min)
        s.add(meeting_ends[name] == meeting_starts[name] + duration)

    # Ensure no overlapping meetings and account for travel times
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i + 1, len(friend_names)):
            name1, name2 = friend_names[i], friend_names[j]
            loc1, loc2 = friends[name1]["location"], friends[name2]["location"]
            travel_time = travel_times[loc1].get(loc2, 0)

            # Either meeting1 is before meeting2 (with travel time) or vice versa
            s.add(Or(
                meeting_ends[name1] + travel_time <= meeting_starts[name2],
                meeting_ends[name2] + travel_time <= meeting_starts[name1]
            ))

    # Starting at The Castro at 9:00 AM
    s.add(meeting_starts["Anthony"] >= time_to_minutes("9:00") + travel_times["The Castro"]["Haight-Ashbury"])

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            start = model[meeting_starts[name]].as_long()
            end = model[meeting_ends[name]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Get the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))