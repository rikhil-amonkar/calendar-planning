import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times matrix (in minutes)
    travel = {
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Financial District"): 5,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Financial District"): 26,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Financial District"): 19,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Financial District"): 23,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Presidio"): 22,
    }

    # Friend data: location, availability start, end, min duration
    friends = [
        {"name": "Mary", "location": "Golden Gate Park", "start": "8:45", "end": "11:45", "min_duration": 45},
        {"name": "Kevin", "location": "Haight-Ashbury", "start": "10:15", "end": "16:15", "min_duration": 90},
        {"name": "Deborah", "location": "Bayview", "start": "15:00", "end": "19:15", "min_duration": 120},
        {"name": "Stephanie", "location": "Presidio", "start": "10:00", "end": "17:15", "min_duration": 120},
        {"name": "Emily", "location": "Financial District", "start": "11:30", "end": "21:45", "min_duration": 105},
    ]

    # Start at Embarcadero at 9:00
    current_location = "Embarcadero"
    current_time = time_to_minutes("9:00")
    itinerary = []

    # Order of meetings: Mary -> Kevin -> Emily -> Stephanie -> Deborah
    meeting_order = ["Mary", "Kevin", "Emily", "Stephanie", "Deborah"]

    for person_name in meeting_order:
        friend = next(f for f in friends if f["name"] == person_name)
        dest = friend["location"]
        travel_time = travel[(current_location, dest)]
        arrival = current_time + travel_time

        # Adjust start time to within friend's window
        window_start = time_to_minutes(friend["start"])
        window_end = time_to_minutes(friend["end"])
        if arrival < window_start:
            arrival = window_start
        if arrival > window_end:
            # Not feasible in this order, but we know it is from manual check
            raise ValueError(f"Cannot meet {person_name}")

        # Calculate meeting end time
        meeting_end = arrival + friend["min_duration"]
        if meeting_end > window_end:
            raise ValueError(f"Cannot meet {person_name} for full duration")

        # Add to itinerary
        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": person_name,
            "start_time": minutes_to_time(arrival),
            "end_time": minutes_to_time(meeting_end)
        })

        # Update current location and time
        current_location = dest
        current_time = meeting_end

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()