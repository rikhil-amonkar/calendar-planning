from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Lisa": {
            "location": "The Castro",
            "available_start": 19 * 60 + 15,  # 7:15 PM in minutes
            "available_end": 21 * 60 + 15,    # 9:15 PM in minutes
            "min_duration": 120,
        },
        "Daniel": {
            "location": "Nob Hill",
            "available_start": 8 * 60 + 15,   # 8:15 AM in minutes
            "available_end": 11 * 60,         # 11:00 AM in minutes
            "min_duration": 15,
        },
        "Elizabeth": {
            "location": "Presidio",
            "available_start": 21 * 60 + 15,  # 9:15 PM in minutes
            "available_end": 22 * 60 + 15,    # 10:15 PM in minutes
            "min_duration": 45,
        },
        "Steven": {
            "location": "Marina District",
            "available_start": 16 * 60 + 30,  # 4:30 PM in minutes
            "available_end": 20 * 60 + 45,     # 8:45 PM in minutes
            "min_duration": 90,
        },
        "Timothy": {
            "location": "Pacific Heights",
            "available_start": 12 * 60,        # 12:00 PM in minutes
            "available_end": 18 * 60,         # 6:00 PM in minutes
            "min_duration": 90,
        },
        "Ashley": {
            "location": "Golden Gate Park",
            "available_start": 20 * 60 + 45,   # 8:45 PM in minutes
            "available_end": 21 * 60 + 45,     # 9:45 PM in minutes
            "min_duration": 60,
        },
        "Kevin": {
            "location": "Chinatown",
            "available_start": 12 * 60,       # 12:00 PM in minutes
            "available_end": 19 * 60,          # 7:00 PM in minutes
            "min_duration": 30,
        },
        "Betty": {
            "location": "Richmond District",
            "available_start": 13 * 60 + 15,   # 1:15 PM in minutes
            "available_end": 15 * 60 + 45,    # 3:45 PM in minutes
            "min_duration": 30,
        }
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Mission District": {
            "The Castro": 7,
            "Nob Hill": 12,
            "Presidio": 25,
            "Marina District": 19,
            "Pacific Heights": 16,
            "Golden Gate Park": 17,
            "Chinatown": 16,
            "Richmond District": 20,
        },
        "The Castro": {
            "Mission District": 7,
            "Nob Hill": 16,
            "Presidio": 20,
            "Marina District": 21,
            "Pacific Heights": 16,
            "Golden Gate Park": 11,
            "Chinatown": 22,
            "Richmond District": 16,
        },
        "Nob Hill": {
            "Mission District": 13,
            "The Castro": 17,
            "Presidio": 17,
            "Marina District": 11,
            "Pacific Heights": 8,
            "Golden Gate Park": 17,
            "Chinatown": 6,
            "Richmond District": 14,
        },
        "Presidio": {
            "Mission District": 26,
            "The Castro": 21,
            "Nob Hill": 18,
            "Marina District": 11,
            "Pacific Heights": 11,
            "Golden Gate Park": 12,
            "Chinatown": 21,
            "Richmond District": 7,
        },
        "Marina District": {
            "Mission District": 20,
            "The Castro": 22,
            "Nob Hill": 12,
            "Presidio": 10,
            "Pacific Heights": 7,
            "Golden Gate Park": 18,
            "Chinatown": 15,
            "Richmond District": 11,
        },
        "Pacific Heights": {
            "Mission District": 15,
            "The Castro": 16,
            "Nob Hill": 8,
            "Presidio": 11,
            "Marina District": 6,
            "Golden Gate Park": 15,
            "Chinatown": 11,
            "Richmond District": 12,
        },
        "Golden Gate Park": {
            "Mission District": 17,
            "The Castro": 13,
            "Nob Hill": 20,
            "Presidio": 11,
            "Marina District": 16,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Richmond District": 7,
        },
        "Chinatown": {
            "Mission District": 17,
            "The Castro": 22,
            "Nob Hill": 9,
            "Presidio": 19,
            "Marina District": 12,
            "Pacific Heights": 10,
            "Golden Gate Park": 23,
            "Richmond District": 20,
        },
        "Richmond District": {
            "Mission District": 20,
            "The Castro": 16,
            "Nob Hill": 17,
            "Presidio": 7,
            "Marina District": 9,
            "Pacific Heights": 10,
            "Golden Gate Park": 9,
            "Chinatown": 20,
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_starts = {}
    meeting_ends = {}
    for name in friends:
        meeting_starts[name] = Int(f'start_{name}')
        meeting_ends[name] = Int(f'end_{name}')

    # Add constraints for each friend's availability and duration
    for name in friends:
        friend = friends[name]
        s.add(meeting_starts[name] >= friend["available_start"])
        s.add(meeting_ends[name] <= friend["available_end"])
        s.add(meeting_ends[name] - meeting_starts[name] >= friend["min_duration"])

    # Initial current location is Mission District at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = "Mission District"

    # We need to define the order of meetings. Here, we'll try to meet friends in the order that fits constraints.
    # However, since the order isn't specified, we'll need to model possible sequences or use a heuristic.
    # For simplicity, let's assume we can meet Daniel first (since he's available earliest).

    # Let's try to meet Daniel first (since he's available at 8:15 AM, but we arrive at 9:00 AM)
    # Wait, Daniel's available from 8:15 to 11:00 AM. We can meet him after arriving at 9:00 AM.
    # Travel time from Mission District to Nob Hill is 12 minutes.
    # So, arrival at Nob Hill is 9:00 + 12 = 9:12 AM.
    # Daniel's available until 11:00 AM. So, we can meet him from 9:12 AM for at least 15 minutes.

    # Similarly, we'll need to sequence other meetings. But modeling all possible sequences is complex.
    # Instead, we'll define variables for the order and travel times between meetings.

    # To model the sequence, we can use a list of friends in a certain order and add travel time constraints between them.
    # However, without knowing the optimal order, we'll need to try different permutations or use a heuristic.

    # For the sake of this example, let's assume the following order: Daniel, Betty, Kevin, Timothy, Steven, Ashley, Lisa, Elizabeth.
    # This is a heuristic based on their available times.

    order = ["Daniel", "Betty", "Kevin", "Timothy", "Steven", "Ashley", "Lisa", "Elizabeth"]

    # Add constraints for travel times between meetings in the assumed order.
    prev_end = current_time
    prev_location = current_location
    for name in order:
        friend = friends[name]
        travel_time = travel_times[prev_location][friend["location"]]
        s.add(meeting_starts[name] >= prev_end + travel_time)
        prev_end = meeting_ends[name]
        prev_location = friend["location"]

    # Check if all constraints can be satisfied
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start = model.eval(meeting_starts[name]).as_long()
            end = model.eval(meeting_ends[name]).as_long()
            start_hh = start // 60
            start_mm = start % 60
            end_hh = end // 60
            end_mm = end % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        return {"itinerary": itinerary}
    else:
        # If the initial order doesn't work, try a different order
        # Here, we'll try meeting Daniel, Kevin, Betty, Timothy, Steven, Ashley, Lisa, Elizabeth
        s.reset()
        for name in friends:
            s.add(meeting_starts[name] >= friends[name]["available_start"])
            s.add(meeting_ends[name] <= friends[name]["available_end"])
            s.add(meeting_ends[name] - meeting_starts[name] >= friends[name]["min_duration"])

        order = ["Daniel", "Kevin", "Betty", "Timothy", "Steven", "Ashley", "Lisa", "Elizabeth"]
        prev_end = current_time
        prev_location = current_location
        for name in order:
            friend = friends[name]
            travel_time = travel_times[prev_location][friend["location"]]
            s.add(meeting_starts[name] >= prev_end + travel_time)
            prev_end = meeting_ends[name]
            prev_location = friend["location"]

        if s.check() == sat:
            model = s.model()
            itinerary = []
            for name in order:
                start = model.eval(meeting_starts[name]).as_long()
                end = model.eval(meeting_ends[name]).as_long()
                start_hh = start // 60
                start_mm = start % 60
                end_hh = end // 60
                end_mm = end % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Execute the solver
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))