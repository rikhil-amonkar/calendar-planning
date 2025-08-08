from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their constraints
    friends = [
        {
            "name": "Kenneth",
            "location": "Richmond District",
            "available_start": "21:15",  # 9:15 PM
            "available_end": "22:00",    # 10:00 PM
            "min_duration": 30,
        },
        {
            "name": "Lisa",
            "location": "Union Square",
            "available_start": "09:00",
            "available_end": "16:30",
            "min_duration": 45,
        },
        {
            "name": "Joshua",
            "location": "Financial District",
            "available_start": "12:00",
            "available_end": "15:15",
            "min_duration": 15,
        },
        {
            "name": "Nancy",
            "location": "Pacific Heights",
            "available_start": "08:00",
            "available_end": "11:30",
            "min_duration": 90,
        },
        {
            "name": "Andrew",
            "location": "Nob Hill",
            "available_start": "11:30",
            "available_end": "20:15",
            "min_duration": 60,
        },
        {
            "name": "John",
            "location": "Bayview",
            "available_start": "16:45",
            "available_end": "21:30",
            "min_duration": 75,
        }
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Embarcadero at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Embarcadero"

    # Travel times dictionary: (from, to) -> minutes
    travel_times = {
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Bayview"): 21,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Bayview"): 26,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Bayview"): 15,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Bayview"): 19,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Bayview"): 22,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Bayview"): 19,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Nob Hill"): 20,
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meeting_vars.append((friend, start, end))

    # Constraints for each meeting
    for friend, start, end in meeting_vars:
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # Meeting must start and end within friend's availability
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + min_duration)

    # Order of meetings: Nancy, Lisa, Andrew, Joshua, John, Kenneth
    order = [
        ("Nancy", "Pacific Heights"),
        ("Lisa", "Union Square"),
        ("Andrew", "Nob Hill"),
        ("Joshua", "Financial District"),
        ("John", "Bayview"),
        ("Kenneth", "Richmond District")
    ]

    prev_end = current_time
    prev_location = current_location
    itinerary_vars = []

    for friend_name, location in order:
        # Find the friend in meeting_vars
        friend_data = None
        start_var = None
        end_var = None
        for friend, start, end in meeting_vars:
            if friend["name"] == friend_name:
                friend_data = friend
                start_var = start
                end_var = end
                break

        if not friend_data:
            continue

        # Add travel time constraint
        travel_key = (prev_location, location)
        if travel_key in travel_times:
            travel_time = travel_times[travel_key]
        else:
            travel_time = 0  # should not happen

        s.add(start_var >= prev_end + travel_time)

        prev_end = end_var
        prev_location = location

        itinerary_vars.append({
            "person": friend_data["name"],
            "start_var": start_var,
            "end_var": end_var
        })

    # Check feasibility
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for entry in itinerary_vars:
            start_val = model[entry["start_var"]].as_long()
            end_val = model[entry["end_var"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": entry["person"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))