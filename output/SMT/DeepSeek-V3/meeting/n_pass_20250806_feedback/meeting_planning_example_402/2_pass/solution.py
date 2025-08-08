from z3 import *
import datetime
from itertools import permutations

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define travel times (in minutes) as a dictionary
    travel_times = {
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Union Square"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Union Square"): 30,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Union Square"): 16,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Sunset District"): 31,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Union Square"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9,
    }

    # Define the friends and their constraints
    friends = {
        "Sarah": {
            "location": "Haight-Ashbury",
            "available_start": datetime.time(17, 0),
            "available_end": datetime.time(21, 30),
            "min_duration": 105,
        },
        "Patricia": {
            "location": "Sunset District",
            "available_start": datetime.time(17, 0),
            "available_end": datetime.time(19, 45),
            "min_duration": 45,
        },
        "Matthew": {
            "location": "Marina District",
            "available_start": datetime.time(9, 15),
            "available_end": datetime.time(12, 0),
            "min_duration": 15,
        },
        "Joseph": {
            "location": "Financial District",
            "available_start": datetime.time(14, 15),
            "available_end": datetime.time(18, 45),
            "min_duration": 30,
        },
        "Robert": {
            "location": "Union Square",
            "available_start": datetime.time(10, 15),
            "available_end": datetime.time(21, 45),
            "min_duration": 15,
        },
    }

    # Current location starts at Golden Gate Park at 9:00 AM
    current_time = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    current_location = "Golden Gate Park"

    # Convert all times to minutes since 9:00 AM for easier arithmetic
    def time_to_minutes(t):
        return t.hour * 60 + t.minute - 9 * 60  # 9:00 AM is 0

    # Define variables for each meeting's start and end times in minutes since 9:00 AM
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = (start, end)
        # Constraints: start and end within availability
        s.add(start >= time_to_minutes(friends[name]["available_start"]))
        s.add(end <= time_to_minutes(friends[name]["available_end"]))
        # Duration constraint
        s.add(end - start >= friends[name]["min_duration"])

    # Define the order of meetings (we'll try all permutations to find the best one)
    friend_names = list(friends.keys())
    best_schedule = None
    max_meetings = 0

    for order in permutations(friend_names):
        temp_s = Solver()
        # Add all meeting constraints
        for name in friends:
            start, end = meeting_vars[name]
            temp_s.add(start >= time_to_minutes(friends[name]["available_start"]))
            temp_s.add(end <= time_to_minutes(friends[name]["available_end"]))
            temp_s.add(end - start >= friends[name]["min_duration"])

        # Add travel time constraints between meetings
        prev_location = current_location
        prev_end = 0  # Start at 9:00 AM (0 minutes)
        for name in order:
            start, end = meeting_vars[name]
            travel_time = travel_times[(prev_location, friends[name]["location"])]
            temp_s.add(start >= prev_end + travel_time)
            prev_end = end
            prev_location = friends[name]["location"]

        # Check if this order is feasible
        if temp_s.check() == sat:
            m = temp_s.model()
            # Count how many meetings we can have
            meetings_count = sum(1 for name in friends if m[meeting_vars[name][0]] is not None)
            if meetings_count > max_meetings:
                max_meetings = meetings_count
                best_schedule = (order, m)

    if best_schedule:
        order, m = best_schedule
        itinerary = []
        for name in order:
            start_min = m[meeting_vars[name][0]].as_long()
            end_min = m[meeting_vars[name][1]].as_long()
            start_time = (datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0)) + datetime.timedelta(minutes=start_min)).time()
            end_time = (datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0)) + datetime.timedelta(minutes=end_min)).time()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M"),
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem
solution = solve_scheduling_problem()
print(solution)