from z3 import *
import json

def main():
    # Create an Optimize object to maximize the number of meetings scheduled
    opt = Optimize()

    # Define the friends and their constraints
    # Times are measured in minutes after 9:00
    friends = ["Kimberly", "Robert", "Rebecca", "Margaret", "Kenneth"]
    avail_start = {
        "Kimberly": 255,  # 13:15 (9:00 + 255 = 13:15)
        "Robert": 195,    # 12:15
        "Rebecca": 255,   # 13:15
        "Margaret": 30,   # 9:30
        "Kenneth": 630    # 19:30
    }
    avail_end = {
        "Kimberly": 525,  # 16:45
        "Robert": 675,    # 20:15
        "Rebecca": 525,   # 16:45
        "Margaret": 270,  # 13:30
        "Kenneth": 735    # 21:15
    }
    min_duration = {
        "Kimberly": 15,
        "Robert": 15,
        "Rebecca": 75,
        "Margaret": 30,
        "Kenneth": 75
    }
    locations = {
        "Kimberly": "Marina District",
        "Robert": "Chinatown",
        "Rebecca": "Financial District",
        "Margaret": "Bayview",
        "Kenneth": "Union Square"
    }

    # Starting point and time
    start_location = "Richmond District"
    start_time = 0  # 9:00 is time 0

    # Travel times in minutes (as given, they are not necessarily symmetric)
    travel = {
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Bayview"): 26,
        ("Richmond District", "Union Square"): 21,

        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Chinatown"): 16,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,

        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Union Square"): 7,

        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Union Square"): 9,

        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Marina District"): 25,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Union Square"): 17,

        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Bayview"): 15,
    }

    n = len(friends)
    # s[i]: start time (minutes after 9:00) for meeting i
    s = [Int(f"s_{i}") for i in range(n)]
    # chosen[i]: whether we decide to hold the meeting with friend i
    chosen = [Bool(f"chosen_{i}") for i in range(n)]

    # Add constraints for each meeting if it is scheduled
    for i in range(n):
        friend = friends[i]
        loc = locations[friend]
        req = min_duration[friend]
        # If meeting is scheduled, its start time must be within the friend's availability window
        opt.add(Implies(chosen[i], s[i] >= avail_start[friend]))
        opt.add(Implies(chosen[i], s[i] + req <= avail_end[friend]))
        # Also require that the meeting starts after we can reach that location from the starting point.
        travel_from_start = travel[(start_location, loc)]
        opt.add(Implies(chosen[i], s[i] >= start_time + travel_from_start))
        # Ensure non-negative start times if scheduled.
        opt.add(Implies(chosen[i], s[i] >= 0))

    # For any two meetings that are scheduled, ensure they do not overlap and account for travel time.
    # For meetings i and j (i < j), either meeting i finishes, we travel from its location to j, and then meeting j can start,
    # OR meeting j finishes, we travel from its location to i, and then meeting i can start.
    for i in range(n):
        for j in range(i+1, n):
            friend_i = friends[i]
            friend_j = friends[j]
            loc_i = locations[friend_i]
            loc_j = locations[friend_j]
            req_i = min_duration[friend_i]
            req_j = min_duration[friend_j]
            # travel times for i->j and j->i
            travel_ij = travel[(loc_i, loc_j)]
            travel_ji = travel[(loc_j, loc_i)]
            opt.add(
                Implies(
                    And(chosen[i], chosen[j]),
                    Or(s[i] + req_i + travel_ij <= s[j],
                       s[j] + req_j + travel_ji <= s[i])
                )
            )

    # Objective: maximize the total number of meetings scheduled
    total_meetings = Sum([If(chosen[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    # Check for a solution and extract the model
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        # Gather scheduled meetings along with their times and locations
        for i in range(n):
            if is_true(model.evaluate(chosen[i])):
                friend = friends[i]
                start_val = model.evaluate(s[i]).as_long()
                end_val = start_val + min_duration[friend]
                scheduled.append((start_val, end_val, friend, locations[friend]))
        # Sort the meetings in chronological order by start time
        scheduled.sort(key=lambda x: x[0])

        # Helper function: convert minutes (offset from 9:00) to "H:MM" 24-hour format
        def format_time(m):
            total = 9 * 60 + m
            hours = total // 60
            minutes = total % 60
            return f"{hours}:{minutes:02d}"

        itinerary = []
        for start_val, end_val, friend, loc in scheduled:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": friend,
                "start_time": format_time(start_val),
                "end_time": format_time(end_val)
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()