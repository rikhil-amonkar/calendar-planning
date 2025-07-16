from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define all friends and their details
    friends = [
        {"name": "Robert", "location": "Chinatown", "start_window": 7*60 + 45, "end_window": 17*60 + 30, "min_duration": 120},
        {"name": "David", "location": "Sunset District", "start_window": 12*60 + 30, "end_window": 19*60 + 45, "min_duration": 45},
        {"name": "Matthew", "location": "Alamo Square", "start_window": 8*60 + 45, "end_window": 13*60 + 45, "min_duration": 90},
        {"name": "Jessica", "location": "Financial District", "start_window": 9*60 + 30, "end_window": 18*60 + 45, "min_duration": 45},
        {"name": "Melissa", "location": "North Beach", "start_window": 7*60 + 15, "end_window": 16*60 + 45, "min_duration": 45},
        {"name": "Mark", "location": "Embarcadero", "start_window": 15*60 + 15, "end_window": 17*60 + 0, "min_duration": 45},
        {"name": "Deborah", "location": "Presidio", "start_window": 19*60 + 0, "end_window": 19*60 + 45, "min_duration": 45},
        {"name": "Karen", "location": "Golden Gate Park", "start_window": 19*60 + 30, "end_window": 22*60 + 0, "min_duration": 120},
        {"name": "Laura", "location": "Bayview", "start_window": 21*60 + 15, "end_window": 22*60 + 15, "min_duration": 15}
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Richmond District": {
            "Chinatown": 20,
            "Sunset District": 11,
            "Alamo Square": 13,
            "Financial District": 22,
            "North Beach": 17,
            "Embarcadero": 19,
            "Presidio": 7,
            "Golden Gate Park": 9,
            "Bayview": 27
        },
        "Chinatown": {
            "Richmond District": 20,
            "Sunset District": 29,
            "Alamo Square": 17,
            "Financial District": 5,
            "North Beach": 3,
            "Embarcadero": 5,
            "Presidio": 19,
            "Golden Gate Park": 23,
            "Bayview": 20
        },
        "Sunset District": {
            "Richmond District": 12,
            "Chinatown": 30,
            "Alamo Square": 17,
            "Financial District": 30,
            "North Beach": 28,
            "Embarcadero": 30,
            "Presidio": 16,
            "Golden Gate Park": 11,
            "Bayview": 22
        },
        "Alamo Square": {
            "Richmond District": 11,
            "Chinatown": 15,
            "Sunset District": 16,
            "Financial District": 17,
            "North Beach": 15,
            "Embarcadero": 16,
            "Presidio": 17,
            "Golden Gate Park": 9,
            "Bayview": 16
        },
        "Financial District": {
            "Richmond District": 21,
            "Chinatown": 5,
            "Sunset District": 30,
            "Alamo Square": 17,
            "North Beach": 7,
            "Embarcadero": 4,
            "Presidio": 22,
            "Golden Gate Park": 23,
            "Bayview": 19
        },
        "North Beach": {
            "Richmond District": 18,
            "Chinatown": 6,
            "Sunset District": 27,
            "Alamo Square": 16,
            "Financial District": 8,
            "Embarcadero": 6,
            "Presidio": 17,
            "Golden Gate Park": 22,
            "Bayview": 25
        },
        "Embarcadero": {
            "Richmond District": 21,
            "Chinatown": 7,
            "Sunset District": 30,
            "Alamo Square": 19,
            "Financial District": 5,
            "North Beach": 5,
            "Presidio": 20,
            "Golden Gate Park": 25,
            "Bayview": 21
        },
        "Presidio": {
            "Richmond District": 7,
            "Chinatown": 21,
            "Sunset District": 15,
            "Alamo Square": 19,
            "Financial District": 23,
            "North Beach": 18,
            "Embarcadero": 20,
            "Golden Gate Park": 12,
            "Bayview": 31
        },
        "Golden Gate Park": {
            "Richmond District": 7,
            "Chinatown": 23,
            "Sunset District": 10,
            "Alamo Square": 9,
            "Financial District": 26,
            "North Beach": 23,
            "Embarcadero": 25,
            "Presidio": 11,
            "Bayview": 23
        },
        "Bayview": {
            "Richmond District": 25,
            "Chinatown": 19,
            "Sunset District": 23,
            "Alamo Square": 16,
            "Financial District": 19,
            "North Beach": 22,
            "Embarcadero": 19,
            "Presidio": 32,
            "Golden Gate Park": 22
        }
    }

    # Create variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    start_vars = {}
    end_vars = {}
    meet_vars = {}  # Boolean variables indicating whether the friend is met
    for friend in friends:
        name = friend["name"]
        start_vars[name] = Int(f"start_{name}")
        end_vars[name] = Int(f"end_{name}")
        meet_vars[name] = Bool(f"meet_{name}")

    # Current location starts at Richmond District at time 0 (9:00 AM)
    current_location = "Richmond District"
    current_time = 0

    # Constraints for each friend
    for friend in friends:
        name = friend["name"]
        location = friend["location"]
        start_window = friend["start_window"] - 9*60  # Convert to minutes since 9:00 AM
        end_window = friend["end_window"] - 9*60
        min_duration = friend["min_duration"]

        # If meeting the friend, their start and end times must be within their window and duration met
        s.add(Implies(meet_vars[name], start_vars[name] >= start_window))
        s.add(Implies(meet_vars[name], end_vars[name] <= end_window))
        s.add(Implies(meet_vars[name], end_vars[name] == start_vars[name] + min_duration))

    # Order of meetings and travel times
    # We need to sequence the meetings, considering travel times
    # This is complex; one approach is to enforce that for any two meetings, one is before the other with travel time in between
    # But this is computationally expensive. Instead, we can try to find a feasible order.
    # For simplicity, we'll assume that the order is determined by the earliest possible start time.

    # To manage this, we'll create a list of all possible meeting sequences and try to find a feasible one.
    # However, this is not straightforward in Z3. Instead, we'll use a heuristic approach.

    # For now, we'll proceed by adding constraints that for any two meetings, if both are met, one must be before the other with travel time.
    # This is a pairwise constraint.
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            friend1 = friends[i]
            friend2 = friends[j]
            name1 = friend1["name"]
            name2 = friend2["name"]
            loc1 = friend1["location"]
            loc2 = friend2["location"]
            travel_time = travel_times[loc1][loc2]

            # Either friend1 is before friend2 or vice versa
            s.add(Implies(And(meet_vars[name1], meet_vars[name2]),
                          Or(end_vars[name1] + travel_time <= start_vars[name2],
                             end_vars[name2] + travel_times[loc2][loc1] <= start_vars[name1])))

    # Ensure that the first meeting starts after arriving at Richmond District (time 0)
    for friend in friends:
        name = friend["name"]
        s.add(Implies(meet_vars[name], start_vars[name] >= 0))

    # Maximize the number of friends met
    total_met = Sum([If(meet_vars[friend["name"]], 1, 0) for friend in friends])
    s.maximize(total_met)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        # Collect all meetings that are scheduled
        scheduled_meetings = []
        for friend in friends:
            name = friend["name"]
            if is_true(m.eval(meet_vars[name])):
                start = m.eval(start_vars[name]).as_long()
                end = m.eval(end_vars[name]).as_long()
                scheduled_meetings.append({
                    "name": name,
                    "location": friend["location"],
                    "start": start,
                    "end": end
                })
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x["start"])
        # Print the schedule
        for meeting in scheduled_meetings:
            start_hour = 9 + meeting["start"] // 60
            start_min = meeting["start"] % 60
            end_hour = 9 + meeting["end"] // 60
            end_min = meeting["end"] % 60
            print(f"Meet {meeting['name']} at {meeting['location']} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()