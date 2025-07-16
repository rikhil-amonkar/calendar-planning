from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and friends
    locations = [
        "Presidio",
        "Fisherman's Wharf",
        "Alamo Square",
        "Financial District",
        "Union Square",
        "Sunset District",
        "Embarcadero",
        "Golden Gate Park",
        "Chinatown",
        "Richmond District"
    ]

    friends = {
        "Jeffrey": {"location": "Fisherman's Wharf", "available_start": 10.25, "available_end": 13.0, "min_duration": 1.5},
        "Ronald": {"location": "Alamo Square", "available_start": 7.75, "available_end": 14.75, "min_duration": 2.0},
        "Jason": {"location": "Financial District", "available_start": 10.75, "available_end": 16.0, "min_duration": 1.75},
        "Melissa": {"location": "Union Square", "available_start": 17.75, "available_end": 18.25, "min_duration": 0.25},
        "Elizabeth": {"location": "Sunset District", "available_start": 14.75, "available_end": 17.5, "min_duration": 1.75},
        "Margaret": {"location": "Embarcadero", "available_start": 13.25, "available_end": 19.0, "min_duration": 1.5},
        "George": {"location": "Golden Gate Park", "available_start": 19.0, "available_end": 22.0, "min_duration": 1.25},
        "Richard": {"location": "Chinatown", "available_start": 9.5, "available_end": 21.0, "min_duration": 0.25},
        "Laura": {"location": "Richmond District", "available_start": 9.75, "available_end": 18.0, "min_duration": 1.0}
    }

    # Travel times dictionary (simplified for this example)
    travel_times = {
        ("Presidio", "Fisherman's Wharf"): 19/60,
        ("Presidio", "Alamo Square"): 19/60,
        ("Presidio", "Financial District"): 23/60,
        ("Presidio", "Union Square"): 22/60,
        ("Presidio", "Sunset District"): 15/60,
        ("Presidio", "Embarcadero"): 20/60,
        ("Presidio", "Golden Gate Park"): 12/60,
        ("Presidio", "Chinatown"): 21/60,
        ("Presidio", "Richmond District"): 7/60,
        ("Fisherman's Wharf", "Presidio"): 17/60,
        ("Fisherman's Wharf", "Alamo Square"): 21/60,
        ("Fisherman's Wharf", "Financial District"): 11/60,
        ("Fisherman's Wharf", "Union Square"): 13/60,
        ("Fisherman's Wharf", "Sunset District"): 27/60,
        ("Fisherman's Wharf", "Embarcadero"): 8/60,
        ("Fisherman's Wharf", "Golden Gate Park"): 25/60,
        ("Fisherman's Wharf", "Chinatown"): 12/60,
        ("Fisherman's Wharf", "Richmond District"): 18/60,
        ("Alamo Square", "Presidio"): 17/60,
        ("Alamo Square", "Fisherman's Wharf"): 19/60,
        ("Alamo Square", "Financial District"): 17/60,
        ("Alamo Square", "Union Square"): 14/60,
        ("Alamo Square", "Sunset District"): 16/60,
        ("Alamo Square", "Embarcadero"): 16/60,
        ("Alamo Square", "Golden Gate Park"): 9/60,
        ("Alamo Square", "Chinatown"): 15/60,
        ("Alamo Square", "Richmond District"): 11/60,
        ("Financial District", "Presidio"): 22/60,
        ("Financial District", "Fisherman's Wharf"): 10/60,
        ("Financial District", "Alamo Square"): 17/60,
        ("Financial District", "Union Square"): 9/60,
        ("Financial District", "Sunset District"): 30/60,
        ("Financial District", "Embarcadero"): 4/60,
        ("Financial District", "Golden Gate Park"): 23/60,
        ("Financial District", "Chinatown"): 5/60,
        ("Financial District", "Richmond District"): 21/60,
        ("Union Square", "Presidio"): 24/60,
        ("Union Square", "Fisherman's Wharf"): 15/60,
        ("Union Square", "Alamo Square"): 15/60,
        ("Union Square", "Financial District"): 9/60,
        ("Union Square", "Sunset District"): 27/60,
        ("Union Square", "Embarcadero"): 11/60,
        ("Union Square", "Golden Gate Park"): 22/60,
        ("Union Square", "Chinatown"): 7/60,
        ("Union Square", "Richmond District"): 20/60,
        ("Sunset District", "Presidio"): 16/60,
        ("Sunset District", "Fisherman's Wharf"): 29/60,
        ("Sunset District", "Alamo Square"): 17/60,
        ("Sunset District", "Financial District"): 30/60,
        ("Sunset District", "Union Square"): 30/60,
        ("Sunset District", "Embarcadero"): 30/60,
        ("Sunset District", "Golden Gate Park"): 11/60,
        ("Sunset District", "Chinatown"): 30/60,
        ("Sunset District", "Richmond District"): 12/60,
        ("Embarcadero", "Presidio"): 20/60,
        ("Embarcadero", "Fisherman's Wharf"): 6/60,
        ("Embarcadero", "Alamo Square"): 19/60,
        ("Embarcadero", "Financial District"): 5/60,
        ("Embarcadero", "Union Square"): 10/60,
        ("Embarcadero", "Sunset District"): 30/60,
        ("Embarcadero", "Golden Gate Park"): 25/60,
        ("Embarcadero", "Chinatown"): 7/60,
        ("Embarcadero", "Richmond District"): 21/60,
        ("Golden Gate Park", "Presidio"): 11/60,
        ("Golden Gate Park", "Fisherman's Wharf"): 24/60,
        ("Golden Gate Park", "Alamo Square"): 9/60,
        ("Golden Gate Park", "Financial District"): 26/60,
        ("Golden Gate Park", "Union Square"): 22/60,
        ("Golden Gate Park", "Sunset District"): 10/60,
        ("Golden Gate Park", "Embarcadero"): 25/60,
        ("Golden Gate Park", "Chinatown"): 23/60,
        ("Golden Gate Park", "Richmond District"): 7/60,
        ("Chinatown", "Presidio"): 19/60,
        ("Chinatown", "Fisherman's Wharf"): 8/60,
        ("Chinatown", "Alamo Square"): 17/60,
        ("Chinatown", "Financial District"): 5/60,
        ("Chinatown", "Union Square"): 7/60,
        ("Chinatown", "Sunset District"): 29/60,
        ("Chinatown", "Embarcadero"): 5/60,
        ("Chinatown", "Golden Gate Park"): 23/60,
        ("Chinatown", "Richmond District"): 20/60,
        ("Richmond District", "Presidio"): 7/60,
        ("Richmond District", "Fisherman's Wharf"): 18/60,
        ("Richmond District", "Alamo Square"): 13/60,
        ("Richmond District", "Financial District"): 22/60,
        ("Richmond District", "Union Square"): 21/60,
        ("Richmond District", "Sunset District"): 11/60,
        ("Richmond District", "Embarcadero"): 19/60,
        ("Richmond District", "Golden Gate Park"): 9/60,
        ("Richmond District", "Chinatown"): 20/60
    }

    # Create variables for each friend's meeting start and end times
    meeting_starts = {name: Real(f'start_{name}') for name in friends}
    meeting_ends = {name: Real(f'end_{name}') for name in friends}

    # Current location starts at Presidio at 9:00 AM (9.0)
    current_location = "Presidio"
    current_time = 9.0

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(meeting_starts[name] >= friend["available_start"])
        s.add(meeting_ends[name] <= friend["available_end"])
        s.add(meeting_ends[name] - meeting_starts[name] >= friend["min_duration"])

    # Ensure meetings do not overlap and account for travel time
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # Travel time between locations
                loc1 = friends[name1]["location"]
                loc2 = friends[name2]["location"]
                travel_time = travel_times.get((loc1, loc2), 0)
                # Either meeting1 ends before meeting2 starts plus travel time, or vice versa
                s.add(Or(
                    meeting_ends[name1] + travel_time <= meeting_starts[name2],
                    meeting_ends[name2] + travel_time <= meeting_starts[name1]
                ))

    # First meeting must be after arrival at Presidio (9:00 AM)
    for name in friends:
        loc = friends[name]["location"]
        travel_time = travel_times.get((current_location, loc), 0)
        s.add(meeting_starts[name] >= current_time + travel_time)

    # Maximize the number of friends met (sum of meeting durations)
    total_duration = Sum([meeting_ends[name] - meeting_starts[name] for name in friends])
    s.maximize(total_duration)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        for name in sorted(friends.keys(), key=lambda x: m[meeting_starts[x]].as_decimal(10)):
            start = m[meeting_starts[name]].as_decimal(10)
            end = m[meeting_ends[name]].as_decimal(10)
            duration = float(end) - float(start)
            print(f"{name}: {start} to {end} (Duration: {duration:.2f} hours) at {friends[name]['location']}")
    else:
        print("No feasible schedule found.")

solve_scheduling()