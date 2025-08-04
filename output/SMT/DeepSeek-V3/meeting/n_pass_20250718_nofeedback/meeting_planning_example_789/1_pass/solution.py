from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Betty", "location": "Russian Hill", "available_start": "07:00", "available_end": "16:45", "min_duration": 105},
        {"name": "Melissa", "location": "Alamo Square", "available_start": "09:30", "available_end": "17:15", "min_duration": 105},
        {"name": "Joshua", "location": "Haight-Ashbury", "available_start": "12:15", "available_end": "19:00", "min_duration": 90},
        {"name": "Jeffrey", "location": "Marina District", "available_start": "12:15", "available_end": "18:00", "min_duration": 45},
        {"name": "James", "location": "Bayview", "available_start": "07:30", "available_end": "20:00", "min_duration": 90},
        {"name": "Anthony", "location": "Chinatown", "available_start": "11:45", "available_end": "13:30", "min_duration": 75},
        {"name": "Timothy", "location": "Presidio", "available_start": "12:30", "available_end": "14:45", "min_duration": 90},
        {"name": "Emily", "location": "Sunset District", "available_start": "19:30", "available_end": "21:30", "min_duration": 120}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define travel times (in minutes)
    travel_times = {
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Sunset District"): 19,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Sunset District"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 16,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Presidio"): 16
    }

    # Define variables for each meeting's start and end times
    meetings = {}
    for friend in friends:
        name = friend["name"]
        meetings[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "location": friend["location"],
            "available_start": time_to_minutes(friend["available_start"]),
            "available_end": time_to_minutes(friend["available_end"]),
            "min_duration": friend["min_duration"]
        }

    # Add constraints for each meeting
    for name, meeting in meetings.items():
        s.add(meeting["start"] >= meeting["available_start"])
        s.add(meeting["end"] <= meeting["available_end"])
        s.add(meeting["end"] - meeting["start"] >= meeting["min_duration"])

    # Add constraints for travel times between meetings
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            name1 = friends[i]["name"]
            name2 = friends[j]["name"]
            loc1 = meetings[name1]["location"]
            loc2 = meetings[name2]["location"]
            travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
            
            # Ensure no overlap and travel time is accounted for
            s.add(Or(
                meetings[name1]["end"] + travel_time <= meetings[name2]["start"],
                meetings[name2]["end"] + travel_time <= meetings[name1]["start"]
            ))

    # Starting point: Union Square at 9:00 AM (540 minutes)
    s.add(meetings["Betty"]["start"] >= 540 + travel_times[("Union Square", "Russian Hill")])
    s.add(meetings["Melissa"]["start"] >= 540 + travel_times[("Union Square", "Alamo Square")])
    s.add(meetings["Joshua"]["start"] >= 540 + travel_times[("Union Square", "Haight-Ashbury")])
    s.add(meetings["Jeffrey"]["start"] >= 540 + travel_times[("Union Square", "Marina District")])
    s.add(meetings["James"]["start"] >= 540 + travel_times[("Union Square", "Bayview")])
    s.add(meetings["Anthony"]["start"] >= 540 + travel_times[("Union Square", "Chinatown")])
    s.add(meetings["Timothy"]["start"] >= 540 + travel_times[("Union Square", "Presidio")])
    s.add(meetings["Emily"]["start"] >= 540 + travel_times[("Union Square", "Sunset District")])

    # Optimize to maximize the number of meetings
    # We'll prioritize meetings with higher min_duration
    # This is a heuristic; in practice, you might need a more sophisticated approach
    s.push()
    s.check()
    model = s.model()

    # Extract the schedule
    itinerary = []
    for name, meeting in meetings.items():
        start = model[meeting["start"]].as_long()
        end = model[meeting["end"]].as_long()
        if start >= 0 and end >= 0:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })

    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))

    return {"itinerary": itinerary}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))