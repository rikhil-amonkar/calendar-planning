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

    # Convert time strings to minutes since midnight
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
            "min_duration": friend["min_duration"],
            "scheduled": Bool(f"scheduled_{name}")
        }

    # Current location starts at Union Square at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Union Square"

    # Add constraints for each meeting
    for name, meeting in meetings.items():
        # Meeting can only be scheduled if it fits in the available window
        s.add(Implies(meeting["scheduled"], 
                      And(meeting["start"] >= meeting["available_start"],
                          meeting["end"] <= meeting["available_end"],
                          meeting["end"] - meeting["start"] >= meeting["min_duration"])))
        
        # If not scheduled, set start and end to 0
        s.add(Implies(Not(meeting["scheduled"]), 
              And(meeting["start"] == 0, meeting["end"] == 0)))

    # Add constraints for travel times between meetings
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            name1 = friends[i]["name"]
            name2 = friends[j]["name"]
            loc1 = meetings[name1]["location"]
            loc2 = meetings[name2]["location"]
            
            # Get travel time between locations
            travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
            
            # If both meetings are scheduled, ensure proper ordering with travel time
            s.add(Implies(And(meetings[name1]["scheduled"], meetings[name2]["scheduled"]),
                  Or(meetings[name1]["end"] + travel_time <= meetings[name2]["start"],
                     meetings[name2]["end"] + travel_time <= meetings[name1]["start"])))

    # Starting point constraints
    for name, meeting in meetings.items():
        travel_time = travel_times.get((current_location, meeting["location"]), 0)
        s.add(Implies(meeting["scheduled"],
                      meeting["start"] >= current_time + travel_time))

    # Optimize to maximize the number of scheduled meetings
    opt = Optimize()
    for name, meeting in meetings.items():
        opt.add_soft(meeting["scheduled"], 1)  # Try to schedule each meeting

    # Add all constraints to the optimizer
    opt.add(s.assertions())

    # Check for satisfiability
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        
        # Extract the schedule
        scheduled_meetings = []
        for name, meeting in meetings.items():
            if is_true(model[meeting["scheduled"]]):
                start = model[meeting["start"]].as_long()
                end = model[meeting["end"]].as_long()
                scheduled_meetings.append({
                    "name": name,
                    "start": start,
                    "end": end,
                    "location": meeting["location"]
                })

        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x["start"])

        # Create itinerary
        for meeting in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })

        return {"itinerary": itinerary}
    else:
        # Return empty itinerary if no solution found
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))