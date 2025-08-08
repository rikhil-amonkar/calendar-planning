from z3 import *
import datetime

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define friends and their details
    friends = {
        "Karen": {
            "location": "Nob Hill",
            "available_start": datetime.time(21, 15),  # 9:15 PM
            "available_end": datetime.time(21, 45),    # 9:45 PM
            "duration": 30  # minutes
        },
        "Joseph": {
            "location": "Haight-Ashbury",
            "available_start": datetime.time(12, 30),
            "available_end": datetime.time(19, 45),
            "duration": 90
        },
        "Sandra": {
            "location": "Chinatown",
            "available_start": datetime.time(7, 15),
            "available_end": datetime.time(19, 15),
            "duration": 75
        },
        "Nancy": {
            "location": "Marina District",
            "available_start": datetime.time(11, 0),
            "available_end": datetime.time(20, 15),
            "duration": 105
        }
    }

    # Travel times (in minutes) between locations
    travel_times = {
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Marina District"): 18,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Marina District"): 11,
        ("Haight-Ashbury", "Union Square"): 17,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Nob Hill"): 8,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Marina District"): 12,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Chinatown"): 16
    }

    # Current location starts at Union Square at 9:00 AM
    current_time = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    current_location = "Union Square"

    # Create variables for each meeting
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {
            "start": start,
            "end": end,
            "location": friends[name]["location"],
            "duration": friends[name]["duration"],
            "available_start": friends[name]["available_start"],
            "available_end": friends[name]["available_end"]
        }
        # Constrain meeting to be within friend's availability
        s.add(start >= (friends[name]["available_start"].hour * 60 + friends[name]["available_start"].minute))
        s.add(end <= (friends[name]["available_end"].hour * 60 + friends[name]["available_end"].minute))
        s.add(end == start + friends[name]["duration"])

    # Ensure meetings do not overlap and account for travel time
    names = list(meetings.keys())
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            name1 = names[i]
            name2 = names[j]
            loc1 = meetings[name1]["location"]
            loc2 = meetings[name2]["location"]
            travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
            # Either meeting1 is before meeting2 or vice versa
            s.add(Or(
                meetings[name1]["end"] + travel_time <= meetings[name2]["start"],
                meetings[name2]["end"] + travel_time <= meetings[name1]["start"]
            ))

    # Ensure meetings are feasible from starting point
    for name in names:
        loc = meetings[name]["location"]
        travel_time = travel_times.get((current_location, loc), 0)
        s.add(meetings[name]["start"] >= (current_time.hour * 60 + current_time.minute + travel_time))

    # Maximize the number of meetings (though all 4 are possible here)
    s.maximize(Sum([If(meetings[name]["start"] >= 0, 1, 0) for name in names]))

    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in names:
            start_val = m[meetings[name]["start"]].as_long()
            end_val = m[meetings[name]["end"]].as_long()
            start_time = datetime.time(start_val // 60, start_val % 60)
            end_time = datetime.time(end_val // 60, end_val % 60)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M")
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)