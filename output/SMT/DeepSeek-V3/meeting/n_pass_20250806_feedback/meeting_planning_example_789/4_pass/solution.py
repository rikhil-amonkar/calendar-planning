from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the optimizer (instead of solver)
    opt = Optimize()

    # Define the friends and their details
    friends = [
        {"name": "Betty", "location": "Russian Hill", "available_start": "7:00", "available_end": "16:45", "min_duration": 105},
        {"name": "Melissa", "location": "Alamo Square", "available_start": "9:30", "available_end": "17:15", "min_duration": 105},
        {"name": "Joshua", "location": "Haight-Ashbury", "available_start": "12:15", "available_end": "19:00", "min_duration": 90},
        {"name": "Jeffrey", "location": "Marina District", "available_start": "12:15", "available_end": "18:00", "min_duration": 45},
        {"name": "James", "location": "Bayview", "available_start": "7:30", "available_end": "20:00", "min_duration": 90},
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

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend["min_duration"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        
        # Add constraints for meeting duration and availability
        opt.add(start >= available_start)
        opt.add(end <= available_end)
        opt.add(end == start + duration)
        
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "duration": duration
        })

    # Starting at Union Square at 9:00 AM (540 minutes)
    opt.add(meetings[0]["start"] >= 540)

    # Define a variable to represent the order of meetings
    order = [Int(f"order_{friend['name']}") for friend in friends]
    opt.add(Distinct(order))
    for i in range(len(order)):
        opt.add(order[i] >= 0, order[i] < len(friends))

    # Add constraints for travel times between consecutive meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # Ensure that if meeting i comes before meeting j, there's enough time to travel
                opt.add(Implies(
                    order[i] < order[j],
                    meetings[j]["start"] >= meetings[i]["end"] + travel_times.get(
                        (meetings[i]["location"], meetings[j]["location"]), 0)
                ))

    # Maximize the number of friends met
    num_met = Int("num_met")
    opt.add(num_met == Sum([If(meetings[i]["start"] >= 0, 1, 0) for i in range(len(friends))]))
    opt.maximize(num_met)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for meeting in meetings:
            start_time = model.evaluate(meeting["start"])
            end_time = model.evaluate(meeting["end"])
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_time.as_long()),
                "end_time": minutes_to_time(end_time.as_long())
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))