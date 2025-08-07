from z3 import *
import json
from collections import defaultdict

def solve_scheduling():
    # Initialize Z3 solver with optimization
    opt = Optimize()

    # Define travel times as a dictionary for easy lookup
    travel_times = {
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Pacific Heights"): 23,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Pacific Heights"): 8,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Pacific Heights"): 11,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Pacific Heights"): 10,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Chinatown"): 11,
    }

    # Define friends and their constraints, ordered by priority
    friends = [
        {"name": "Matthew", "location": "Presidio", "start": "08:15", "end": "09:00", "min_duration": 15},
        {"name": "Richard", "location": "Fisherman's Wharf", "start": "11:00", "end": "12:45", "min_duration": 60},
        {"name": "Elizabeth", "location": "Nob Hill", "start": "11:45", "end": "18:30", "min_duration": 75},
        {"name": "Anthony", "location": "Pacific Heights", "start": "14:15", "end": "16:00", "min_duration": 30},
        {"name": "Brian", "location": "North Beach", "start": "13:00", "end": "19:00", "min_duration": 90},
        {"name": "Kenneth", "location": "Chinatown", "start": "13:45", "end": "19:30", "min_duration": 105},
        {"name": "Ashley", "location": "Haight-Ashbury", "start": "15:00", "end": "20:30", "min_duration": 90},
        {"name": "Kimberly", "location": "Alamo Square", "start": "17:30", "end": "21:15", "min_duration": 45},
        {"name": "Deborah", "location": "Union Square", "start": "17:30", "end": "22:00", "min_duration": 60},
        {"name": "Jessica", "location": "Golden Gate Park", "start": "20:00", "end": "21:45", "min_duration": 105},
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting
    meeting_vars = []
    for friend in friends:
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        start = Int(f"{friend['name']}_start")
        end = Int(f"{friend['name']}_end")
        duration = end - start
        opt.add(start >= start_min)
        opt.add(end <= end_min)
        opt.add(duration >= friend["min_duration"])
        meeting_vars.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "met": Bool(f"met_{friend['name']}")  # Whether we meet this friend
        })
        opt.add_soft(meeting_vars[-1]["met"])  # Try to meet everyone

    # Add constraints for travel times between meetings
    for i in range(len(meeting_vars)):
        for j in range(len(meeting_vars)):
            if i != j:
                # Either meeting i is before j or vice versa
                before = Bool(f"before_{i}_{j}")
                opt.add(before == (meeting_vars[i]["end"] + 
                      travel_times.get((meeting_vars[i]["location"], meeting_vars[j]["location"]), 0) 
                      <= meeting_vars[j]["start"]))
                opt.add(Or(
                    before,
                    meeting_vars[j]["end"] + 
                    travel_times.get((meeting_vars[j]["location"], meeting_vars[i]["location"]), 0) 
                    <= meeting_vars[i]["start"]
                ))

    # Special constraint for Matthew (must be first meeting)
    opt.add(meeting_vars[0]["name"] == "Matthew")
    opt.add(meeting_vars[0]["start"] >= time_to_minutes("09:00"))  # After arrival

    # Optimize to maximize number of friends met
    opt.maximize(Sum([If(var["met"], 1, 0) for var in meeting_vars]))

    # Check if the problem is satisfiable
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for var in meeting_vars:
            if is_true(model[var["met"]]):
                start_time = model[var["start"]].as_long()
                end_time = model[var["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": var["name"],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time),
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))