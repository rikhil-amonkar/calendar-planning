from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define the friends and their constraints
    friends = {
        "Kimberly": {"location": "North Beach", "available_start": "07:00", "available_end": "10:30", "duration": 15},
        "Brian": {"location": "Fisherman's Wharf", "available_start": "09:30", "available_end": "15:30", "duration": 45},
        "Kenneth": {"location": "Nob Hill", "available_start": "12:15", "available_end": "17:15", "duration": 105},
        "Joshua": {"location": "Presidio", "available_start": "16:30", "available_end": "18:15", "duration": 105},
        "Joseph": {"location": "Embarcadero", "available_start": "15:30", "available_end": "19:30", "duration": 75},
        "Betty": {"location": "Haight-Ashbury", "available_start": "19:00", "available_end": "20:30", "duration": 90},
        "Steven": {"location": "Mission District", "available_start": "19:30", "available_end": "21:00", "duration": 90},
        "Melissa": {"location": "The Castro", "available_start": "20:15", "available_end": "21:15", "duration": 30},
        "Barbara": {"location": "Alamo Square", "available_start": "20:45", "available_end": "21:45", "duration": 15}
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define travel times (in minutes)
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
        ("Haight-Ashbury", "Mission District"): 11
    }

    # Create Z3 variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = {"start": start, "end": end}

    # Add constraints for each meeting
    for name in friends:
        friend = friends[name]
        start = meeting_vars[name]["start"]
        end = meeting_vars[name]["end"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        duration = friend["duration"]

        # Meeting must be within available time
        opt.add(start >= available_start)
        opt.add(end <= available_end)
        opt.add(end == start + duration)

    # Add constraints for travel times between meetings
    names = list(friends.keys())
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            name1 = names[i]
            name2 = names[j]
            loc1 = friends[name1]["location"]
            loc2 = friends[name2]["location"]
            travel_time = travel_times.get((loc1, loc2), 0)
            
            # Add buffer time (10 minutes) between meetings
            opt.add(Or(
                meeting_vars[name1]["end"] + travel_time + 10 <= meeting_vars[name2]["start"],
                meeting_vars[name2]["end"] + travel_time + 10 <= meeting_vars[name1]["start"]
            ))

    # Prioritize meetings with tighter time windows first
    priority_order = sorted(friends.keys(), key=lambda x: (
        time_to_minutes(friends[x]["available_end"]) - time_to_minutes(friends[x]["available_start"]),
        friends[x]["duration"]
    ))

    # Add soft constraints to prioritize certain meetings
    for i, name in enumerate(priority_order):
        opt.add_soft(meeting_vars[name]["start"] >= 0, weight=len(priority_order)-i)

    # Check if the constraints are satisfiable
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            start_val = m[meeting_vars[name]["start"]]
            end_val = m[meeting_vars[name]["end"]]
            if start_val is not None and end_val is not None:
                start = start_val.as_long()
                end = end_val.as_long()
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
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))