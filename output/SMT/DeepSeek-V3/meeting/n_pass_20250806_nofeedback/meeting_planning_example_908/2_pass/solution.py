from z3 import *
import json

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {"name": "Mark", "location": "Fisherman's Wharf", "available_start": "8:15", "available_end": "10:00", "duration": 30},
        {"name": "Stephanie", "location": "Presidio", "available_start": "12:15", "available_end": "15:00", "duration": 75},
        {"name": "Betty", "location": "Bayview", "available_start": "7:15", "available_end": "20:30", "duration": 15},
        {"name": "Lisa", "location": "Haight-Ashbury", "available_start": "15:30", "available_end": "18:30", "duration": 45},
        {"name": "William", "location": "Russian Hill", "available_start": "18:45", "available_end": "20:00", "duration": 60},
        {"name": "Brian", "location": "The Castro", "available_start": "9:15", "available_end": "13:15", "duration": 30},
        {"name": "Joseph", "location": "Marina District", "available_start": "10:45", "available_end": "15:00", "duration": 90},
        {"name": "Ashley", "location": "Richmond District", "available_start": "9:45", "available_end": "11:15", "duration": 45},
        {"name": "Patricia", "location": "Union Square", "available_start": "16:30", "available_end": "20:00", "duration": 120},
        {"name": "Karen", "location": "Sunset District", "available_start": "16:30", "available_end": "22:00", "duration": 105}
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

    # Travel times dictionary (simplified for this example)
    travel_times = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        # Add reverse travel times
        ("Fisherman's Wharf", "Financial District"): 10,
        ("Presidio", "Financial District"): 22,
        ("Bayview", "Financial District"): 19,
        ("Haight-Ashbury", "Financial District"): 19,
        ("Russian Hill", "Financial District"): 11,
        ("The Castro", "Financial District"): 20,
        ("Marina District", "Financial District"): 15,
        ("Richmond District", "Financial District"): 21,
        ("Union Square", "Financial District"): 9,
        ("Sunset District", "Financial District"): 30,
        # Add other travel times as needed
    }

    # Create variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        duration = friend["duration"]
        
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "available_start": available_start,
            "available_end": available_end,
            "duration": duration
        })
        
        # Convert Python integers to Z3 constants
        s.add(start >= IntVal(available_start))
        s.add(end <= IntVal(available_end))
        s.add(end == start + IntVal(duration))

    # Add constraints for travel times between meetings
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                # Get travel time between locations
                loc1 = meetings[i]["location"]
                loc2 = meetings[j]["location"]
                travel_time = travel_times.get((loc1, loc2), 0)
                
                # Ensure enough time between meetings
                s.add(Or(
                    meetings[j]["start"] >= meetings[i]["end"] + IntVal(travel_time),
                    meetings[i]["start"] >= meetings[j]["end"] + IntVal(travel_time)
                ))

    # Initial constraint: start at Financial District at 9:00 AM (540 minutes)
    arrival_time = IntVal(540)  # 9:00 AM in minutes
    if len(meetings) > 0:
        s.add(meetings[0]["start"] >= arrival_time)

    # Try to solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for meeting in meetings:
            start_val = m[meeting["start"]].as_long()
            end_val = m[meeting["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the scheduling problem
result = solve_scheduling()
print("SOLUTION:")
print(json.dumps(result, indent=2))