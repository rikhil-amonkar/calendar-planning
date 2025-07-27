from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define locations and friends' data
    friends = {
        "Melissa": {"location": "The Castro", "start": 20*60 + 15, "end": 21*60 + 15, "duration": 30},
        "Kimberly": {"location": "North Beach", "start": 7*60 + 0, "end": 10*60 + 30, "duration": 15},
        "Joseph": {"location": "Embarcadero", "start": 15*60 + 30, "end": 19*60 + 30, "duration": 75},
        "Barbara": {"location": "Alamo Square", "start": 20*60 + 45, "end": 21*60 + 45, "duration": 15},
        "Kenneth": {"location": "Nob Hill", "start": 12*60 + 15, "end": 17*60 + 15, "duration": 105},
        "Joshua": {"location": "Presidio", "start": 16*60 + 30, "end": 18*60 + 15, "duration": 105},
        "Brian": {"location": "Fisherman's Wharf", "start": 9*60 + 30, "end": 15*60 + 30, "duration": 45},
        "Steven": {"location": "Mission District", "start": 19*60 + 30, "end": 21*60 + 0, "duration": 90},
        "Betty": {"location": "Haight-Ashbury", "start": 19*60 + 0, "end": 20*60 + 30, "duration": 90}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Union Square": {
            "The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15,
            "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14,
            "Haight-Ashbury": 18
        },
        "The Castro": {
            "Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8,
            "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7,
            "Haight-Ashbury": 6
        },
        "North Beach": {
            "Union Square": 7, "The Castro": 23, "Embarcadero": 6, "Alamo Square": 16,
            "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18,
            "Haight-Ashbury": 18
        },
        "Embarcadero": {
            "Union Square": 10, "The Castro": 25, "North Beach": 5, "Alamo Square": 19,
            "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20,
            "Haight-Ashbury": 21
        },
        "Alamo Square": {
            "Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16,
            "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10,
            "Haight-Ashbury": 5
        },
        "Nob Hill": {
            "Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9,
            "Alamo Square": 11, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13,
            "Haight-Ashbury": 13
        },
        "Presidio": {
            "Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20,
            "Alamo Square": 19, "Nob Hill": 18, "Fisherman's Wharf": 19, "Mission District": 26,
            "Haight-Ashbury": 15
        },
        "Fisherman's Wharf": {
            "Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8,
            "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Mission District": 22,
            "Haight-Ashbury": 22
        },
        "Mission District": {
            "Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19,
            "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22,
            "Haight-Ashbury": 12
        },
        "Haight-Ashbury": {
            "Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20,
            "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23,
            "Mission District": 11
        }
    }

    # Create variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    start_vars = {}
    end_vars = {}
    for name in friends:
        start_vars[name] = Int(f'start_{name}')
        end_vars[name] = Int(f'end_{name}')

    # Current location starts at Union Square at time 0 (9:00 AM)
    current_location = "Union Square"
    current_time = 0

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        s.add(start_vars[name] >= data["start"] - 9*60)  # Convert to minutes since 9:00 AM
        s.add(end_vars[name] <= data["end"] - 9*60)
        s.add(end_vars[name] == start_vars[name] + data["duration"])

    # Define the order of meetings to try
    order = ["Kimberly", "Brian", "Kenneth", "Joseph", "Joshua", "Betty", "Steven", "Barbara", "Melissa"]

    # Add travel time constraints between consecutive meetings
    prev_location = "Union Square"
    prev_end = 0
    for name in order:
        friend_loc = friends[name]["location"]
        travel_time = travel_times[prev_location][friend_loc]
        s.add(start_vars[name] >= prev_end + travel_time)
        prev_end = end_vars[name]
        prev_location = friend_loc

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in order:
            start = m.evaluate(start_vars[name]).as_long()
            end = m.evaluate(end_vars[name]).as_long()
            start_hour = (start + 9*60) // 60
            start_min = (start + 9*60) % 60
            end_hour = (end + 9*60) // 60
            end_min = (end + 9*60) % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hour:02d}:{start_min:02d}",
                "end_time": f"{end_hour:02d}:{end_min:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
solution = solve_scheduling()
print(solution)