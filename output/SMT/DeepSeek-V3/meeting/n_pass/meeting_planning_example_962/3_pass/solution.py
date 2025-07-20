import json
from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    solver = Optimize()

    # Define the friends and their constraints
    friends = [
        {"name": "Elizabeth", "location": "Marina District", "available_start": "19:00", "available_end": "20:45", "min_duration": 105},
        {"name": "Joshua", "location": "Presidio", "available_start": "8:30", "available_end": "13:15", "min_duration": 105},
        {"name": "Timothy", "location": "North Beach", "available_start": "19:45", "available_end": "22:00", "min_duration": 90},
        {"name": "David", "location": "Embarcadero", "available_start": "10:45", "available_end": "12:30", "min_duration": 30},
        {"name": "Kimberly", "location": "Haight-Ashbury", "available_start": "16:45", "available_end": "21:30", "min_duration": 75},
        {"name": "Lisa", "location": "Golden Gate Park", "available_start": "17:30", "available_end": "21:45", "min_duration": 45},
        {"name": "Ronald", "location": "Richmond District", "available_start": "8:00", "available_end": "9:30", "min_duration": 90},
        {"name": "Stephanie", "location": "Alamo Square", "available_start": "15:30", "available_end": "16:30", "min_duration": 30},
        {"name": "Helen", "location": "Financial District", "available_start": "17:30", "available_end": "18:30", "min_duration": 45},
        {"name": "Laura", "location": "Sunset District", "available_start": "17:45", "available_end": "21:15", "min_duration": 90}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Starting time at The Castro
    current_time = time_to_minutes("9:00")

    # Create variables for each friend's meeting start and end times
    meetings = []
    for friend in friends:
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        meet = Bool(f'meet_{friend["name"]}')

        # Constraints for meeting within available time
        solver.add(Implies(meet, start >= available_start))
        solver.add(Implies(meet, end <= available_end))
        solver.add(Implies(meet, end == start + min_duration))
        solver.add(Implies(meet, start + min_duration <= available_end))

        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "meet": meet,
            "min_duration": min_duration
        })

    # Define travel times between locations
    travel_times = {
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Sunset District"): 17,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Sunset District"): 19,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Sunset District"): 15,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Sunset District"): 27,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Sunset District"): 30,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Sunset District"): 11,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Sunset District"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30
    }

    # Define the sequence of meetings (order is to be determined)
    # We'll use a heuristic to prioritize friends with tight time windows
    # Ronald is only available until 9:30 AM, so we must meet him first
    # Then Joshua, David, etc.

    # Define the order manually based on availability
    order = [
        ("Ronald", "Richmond District"),
        ("Joshua", "Presidio"),
        ("David", "Embarcadero"),
        ("Stephanie", "Alamo Square"),
        ("Helen", "Financial District"),
        ("Kimberly", "Haight-Ashbury"),
        ("Lisa", "Golden Gate Park"),
        ("Laura", "Sunset District"),
        ("Elizabeth", "Marina District"),
        ("Timothy", "North Beach")
    ]

    # For each friend in order, add meeting constraints
    prev_end = Int('prev_end_start')
    solver.add(prev_end == current_time)
    prev_location = "The Castro"
    scheduled_meetings = []

    for person, location in order:
        # Find the friend's data
        friend = next(f for f in meetings if f["name"] == person)
        meet = friend["meet"]
        start = friend["start"]
        end = friend["end"]
        min_duration = friend["min_duration"]

        # Travel time from previous location to current location
        travel_time = travel_times.get((prev_location, location), 0)

        # Constraint: if meeting this friend, start >= prev_end + travel_time
        solver.add(Implies(meet, start >= prev_end + travel_time))

        # Add to scheduled meetings if meeting
        scheduled_meetings.append(meet)

        # Update previous end and location if meeting
        new_prev_end = If(meet, end, prev_end)
        new_prev_location = If(meet, location, prev_location)

        prev_end = new_prev_end
        prev_location = new_prev_location

    # Maximize the number of friends met
    solver.maximize(Sum([If(m, 1, 0) for m in scheduled_meetings]))

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []

        # Collect all meetings that are scheduled
        for friend in meetings:
            if is_true(model[friend["meet"]]):
                start_min = model[friend["start"]].as_long()
                end_min = model[friend["end"]].as_long()
                start_time = f"{start_min // 60:02d}:{start_min % 60:02d}"
                end_time = f"{end_min // 60:02d}:{end_min % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })

        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))