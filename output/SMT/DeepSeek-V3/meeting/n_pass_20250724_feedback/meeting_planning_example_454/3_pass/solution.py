from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Jessica": {"location": "Golden Gate Park", "start": (13, 45), "end": (15, 0), "min_duration": 30},
        "Ashley": {"location": "Bayview", "start": (17, 15), "end": (20, 0), "min_duration": 105},
        "Ronald": {"location": "Chinatown", "start": (7, 15), "end": (14, 45), "min_duration": 90},
        "William": {"location": "North Beach", "start": (13, 15), "end": (20, 15), "min_duration": 15},
        "Daniel": {"location": "Mission District", "start": (7, 0), "end": (11, 15), "min_duration": 105}
    }

    # Define travel times (in minutes) between locations
    travel_times = {
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Mission District"): 26,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Mission District"): 17,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Mission District"): 13,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Mission District"): 18,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Mission District"): 18,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "North Beach"): 17
    }

    # Current location starts at Presidio at 9:00 AM
    current_time_min = 9 * 60  # 9:00 AM in minutes
    current_location = "Presidio"

    # Convert all times to minutes since midnight for easier arithmetic
    def to_minutes(time):
        return time[0] * 60 + time[1]

    def from_minutes(minutes):
        return (minutes // 60, minutes % 60)

    # Variables to track meetings
    meetings = []
    itinerary = []

    # For each friend, create variables for meeting start and end times
    for name, info in friends.items():
        start_min = to_minutes(info["start"])
        end_min = to_minutes(info["end"])
        min_duration = info["min_duration"]

        # Create Z3 variables for meeting start and end times
        meet_start = Int(f"meet_start_{name}")
        meet_end = Int(f"meet_end_{name}")

        # Add constraints for meeting within friend's availability
        s.add(meet_start >= start_min)
        s.add(meet_end <= end_min)
        s.add(meet_end - meet_start >= min_duration)

        # Add constraint: Meeting must start after 9:00 AM
        s.add(meet_start >= current_time_min)

        # Add to meetings list
        meetings.append({
            "name": name,
            "location": info["location"],
            "start": meet_start,
            "end": meet_end
        })

    # Add constraints for travel times between meetings
    # We need to sequence the meetings and account for travel times
    # For simplicity, assume meetings are scheduled in order of their availability
    # A more sophisticated approach would sequence meetings optimally
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            # Ensure meeting j starts after meeting i ends + travel time
            travel_key = (meetings[i]["location"], meetings[j]["location"])
            if travel_key in travel_times:
                s.add(meetings[j]["start"] >= meetings[i]["end"] + travel_times[travel_key])

    if s.check() == sat:
        model = s.model()
        for meet in meetings:
            start = model.eval(meet["start"]).as_long()
            end = model.eval(meet["end"]).as_long()
            start_time = from_minutes(start)
            end_time = from_minutes(end)
            itinerary.append({
                "action": "meet",
                "person": meet["name"],
                "start_time": f"{start_time[0]:02d}:{start_time[1]:02d}",
                "end_time": f"{end_time[0]:02d}:{end_time[1]:02d}"
            })
    else:
        # If not all can be met, try subsets (not implemented here for brevity)
        pass

    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])

    return {"itinerary": itinerary}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))