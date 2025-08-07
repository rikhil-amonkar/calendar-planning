from z3 import *
import json
from itertools import combinations

def solve_scheduling():
    s = Optimize()

    # Friends data with availability and duration requirements
    friends = {
        "Melissa": {"location": "The Castro", "available_start": "20:15", "available_end": "21:15", "min_duration": 30},
        "Kimberly": {"location": "North Beach", "available_start": "07:00", "available_end": "10:30", "min_duration": 15},
        "Joseph": {"location": "Embarcadero", "available_start": "15:30", "available_end": "19:30", "min_duration": 75},
        "Barbara": {"location": "Alamo Square", "available_start": "20:45", "available_end": "21:45", "min_duration": 15},
        "Kenneth": {"location": "Nob Hill", "available_start": "12:15", "available_end": "17:15", "min_duration": 105},
        "Joshua": {"location": "Presidio", "available_start": "16:30", "available_end": "18:15", "min_duration": 105},
        "Brian": {"location": "Fisherman's Wharf", "available_start": "09:30", "available_end": "15:30", "min_duration": 45},
        "Steven": {"location": "Mission District", "available_start": "19:30", "available_end": "21:00", "min_duration": 90},
        "Betty": {"location": "Haight-Ashbury", "available_start": "19:00", "available_end": "20:30", "min_duration": 90}
    }

    # Time conversion functions
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times between locations
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

    # Create variables for each meeting
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = {"start": start, "end": end, "location": friends[name]["location"]}

    # Starting point
    current_time = 540  # 9:00 AM in minutes
    current_location = "Union Square"

    # Add basic constraints for each meeting
    for name in friends:
        friend = friends[name]
        start_var = meeting_vars[name]["start"]
        end_var = meeting_vars[name]["end"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Meeting must be within friend's availability
        s.add(start_var >= available_start)
        s.add(end_var <= available_end)
        s.add(end_var == start_var + min_duration)

    # Add travel time constraints between consecutive meetings
    for name1, name2 in combinations(friends.keys(), 2):
        loc1 = meeting_vars[name1]["location"]
        loc2 = meeting_vars[name2]["location"]
        travel_time = travel_times[(loc1, loc2)]
        
        # Ensure enough time between meetings
        s.add(Or(
            meeting_vars[name1]["end"] + travel_time <= meeting_vars[name2]["start"],
            meeting_vars[name2]["end"] + travel_time <= meeting_vars[name1]["start"]
        ))

    # Maximize the number of meetings
    meet_count = Int('meet_count')
    s.add(meet_count == Sum([If(meeting_vars[name]["start"] >= 0, 1, 0) for name in friends]))
    s.maximize(meet_count)

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        scheduled_meetings = []
        
        # Collect all scheduled meetings
        for name in friends:
            if model[meeting_vars[name]["start"]] is not None:
                start_val = model[meeting_vars[name]["start"]].as_long()
                end_val = model[meeting_vars[name]["end"]].as_long()
                scheduled_meetings.append({
                    "name": name,
                    "start": start_val,
                    "end": end_val,
                    "location": meeting_vars[name]["location"]
                })
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x["start"])
        
        # Build itinerary in chronological order
        for meeting in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": [], "error": "No feasible schedule found"}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))