from z3 import *
import json
from itertools import permutations

# Define the friends and their availability
friends = {
    "Laura": {"location": "Alamo Square", "start": "14:30", "end": "16:15", "duration": 75},
    "Brian": {"location": "Presidio", "start": "10:15", "end": "17:00", "duration": 30},
    "Karen": {"location": "Russian Hill", "start": "18:00", "end": "20:15", "duration": 90},
    "Stephanie": {"location": "North Beach", "start": "10:15", "end": "16:00", "duration": 75},
    "Helen": {"location": "Golden Gate Park", "start": "11:30", "end": "21:45", "duration": 120},
    "Sandra": {"location": "Richmond District", "start": "08:00", "end": "15:15", "duration": 30},
    "Mary": {"location": "Embarcadero", "start": "16:45", "end": "18:45", "duration": 120},
    "Deborah": {"location": "Financial District", "start": "19:00", "end": "20:45", "duration": 105},
    "Elizabeth": {"location": "Marina District", "start": "08:30", "end": "13:15", "duration": 105}
}

# Define travel times (in minutes) between locations
travel_times = {
    "Mission District": {
        "Alamo Square": 11,
        "Presidio": 25,
        "Russian Hill": 15,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Financial District": 15,
        "Marina District": 19
    },
    "Alamo Square": {
        "Mission District": 10,
        "Presidio": 17,
        "Russian Hill": 13,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Embarcadero": 16,
        "Financial District": 17,
        "Marina District": 15
    },
    "Presidio": {
        "Mission District": 26,
        "Alamo Square": 19,
        "Russian Hill": 14,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11
    },
    "Russian Hill": {
        "Mission District": 16,
        "Alamo Square": 15,
        "Presidio": 14,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Mission District": 18,
        "Alamo Square": 16,
        "Presidio": 17,
        "Russian Hill": 4,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "Alamo Square": 9,
        "Presidio": 11,
        "Russian Hill": 19,
        "North Beach": 23,
        "Richmond District": 7,
        "Embarcadero": 25,
        "Financial District": 26,
        "Marina District": 16
    },
    "Richmond District": {
        "Mission District": 20,
        "Alamo Square": 13,
        "Presidio": 7,
        "Russian Hill": 13,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "Marina District": 9
    },
    "Embarcadero": {
        "Mission District": 20,
        "Alamo Square": 19,
        "Presidio": 20,
        "Russian Hill": 8,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Financial District": 5,
        "Marina District": 12
    },
    "Financial District": {
        "Mission District": 17,
        "Alamo Square": 17,
        "Presidio": 22,
        "Russian Hill": 11,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Embarcadero": 4,
        "Marina District": 15
    },
    "Marina District": {
        "Mission District": 20,
        "Alamo Square": 15,
        "Presidio": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Financial District": 17
    }
}

# Convert time strings to minutes since 9:00 AM (540 minutes)
def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm - 540  # Subtract 540 to make 9:00 AM as 0

# Convert minutes back to time string
def minutes_to_time(minutes):
    total = minutes + 540
    hh = total // 60
    mm = total % 60
    return f"{hh:02d}:{mm:02d}"

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()

    # Create variables for each meeting's start and end times
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {"start": start, "end": end}

    # Add constraints for each meeting's time window and duration
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        duration = friend["duration"]
        
        solver.add(meetings[name]["start"] >= start_min)
        solver.add(meetings[name]["end"] <= end_min)
        solver.add(meetings[name]["end"] == meetings[name]["start"] + duration)

    # Create a variable to represent the order of meetings
    meeting_order = [Int(f"order_{i}") for i in range(len(friends))]
    
    # Each order variable must be between 0 and len(friends)-1
    for i in range(len(friends)):
        solver.add(meeting_order[i] >= 0)
        solver.add(meeting_order[i] < len(friends))
    
    # All order variables must be distinct
    solver.add(Distinct(meeting_order))
    
    # Add travel time constraints between consecutive meetings
    for i in range(len(friends)-1):
        # Get the current and next meeting based on the order
        current = meeting_order[i]
        next_meeting = meeting_order[i+1]
        
        # For each possible pair of meetings, add the travel time constraint
        for name1 in friends:
            for name2 in friends:
                if name1 != name2:
                    # If current is name1 and next is name2, add travel time constraint
                    solver.add(Implies(
                        And(current == list(friends.keys()).index(name1),
                            next_meeting == list(friends.keys()).index(name2)),
                        meetings[name2]["start"] >= meetings[name1]["end"] + travel_times[friends[name1]["location"]][friends[name2]["location"]]
                    ))

    # Add constraint that the first meeting starts after arrival at Mission District at 9:00 AM (0 minutes)
    solver.add(Or([meetings[name]["start"] >= 0 for name in friends]))

    # Try to find a solution
    if solver.check() == sat:
        model = solver.model()
        
        # Get the actual order of meetings
        order = []
        for i in range(len(friends)):
            for name in friends:
                if model.evaluate(meeting_order[i]).as_long() == list(friends.keys()).index(name):
                    order.append(name)
                    break
        
        # Build the itinerary
        itinerary = []
        for name in order:
            start = model.evaluate(meetings[name]["start"]).as_long()
            end = model.evaluate(meetings[name]["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        
        return {"itinerary": itinerary}
    else:
        return None

# Try different permutations if the first attempt fails
solution = None
for attempt in range(10):  # Try up to 10 different permutations
    solution = solve_scheduling()
    if solution:
        break

if solution:
    print(json.dumps(solution, indent=2))
else:
    print("No valid schedule found after multiple attempts.")