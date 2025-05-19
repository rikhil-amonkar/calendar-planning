# Read input travel times
travel_times = {
    # From Embarcadero (EB)
    "EB": {
        "Golden Gate Park (GGP)": 25,
        "Haight-Ashbury (HA)": 21,
        "Bayview (BV)": 21,
        "Presidio (PR)": 20,
        "Financial District (FD)": 5,
    },
    # From Golden Gate Park (GGP)
    "GGP": {
        "Embarcadero (EB)": 25,
        "Haight-Ashbury (HA)": 7,
        "Bayview (BV)": 23,
        "Presidio (PR)": 11,
        "Financial District (FD)": 26,
    },
    # From Haight-Ashbury (HA)
    "HA": {
        "Embarcadero (EB)": 20,
        "Golden Gate Park (GGP)": 7,
        "Bayview (BV)": 19,
        "Presidio (PR)": 15,
        "Financial District (FD)": 21,
    },
    # From Bayview (BV)
    "BV": {
        "Embarcadero (EB)": 19,
        "Golden Gate Park (GGP)": 22,
        "Haight-Ashbury (HA)": 19,
        "Presidio (PR)": 31,
        "Financial District (FD)": 19,
    },
    # From Presidio (PR)
    "PR": {
        "Embarcadero (EB)": 20,
        "Golden Gate Park (GGP)": 12,
        "Haight-Ashbury (HA)": 15,
        "Bayview (BV)": 31,
        "Financial District (FD)": 23,
    },
    # From Financial District (FD)
    "FD": {
        "Embarcadero (EB)": 4,
        "Golden Gate Park (GGP)": 23,
        "Haight-Ashbury (HA)": 19,
        "Bayview (BV)": 19,
        "Presidio (PR)": 22,
    },
}

# Read constraints
constraints = {
    "Mary": {
        "start": "8:45",
        "end": "11:45",
        "location": "Golden Gate Park (GGP)",
        "duration": 45,
    },
    "Kevin": {
        "start": "10:15",
        "end": "16:15",
        "location": "Haight-Ashbury (HA)",
        "duration": 90,
    },
    "Deborah": {
        "start": "15:00",
        "end": "19:15",
        "location": "Bayview (BV)",
        "duration": 120,
    },
    "Stephanie": {
        "start": "10:00",
        "end": "17:15",
        "location": "Presidio (PR)",
        "duration": 120,
    },
    "Emily": {
        "start": "11:30",
        "end": "21:45",
        "location": "Financial District (FD)",
        "duration": 105,
    },
}

# Starting location is Embarcadero (EB) at 9:00 AM
start_time = "9:00"

def compute_schedule():
    from datetime import datetime, timedelta
    import itertools

    # Convert times to minutes since 9:00 AM
    def time_to_min(t):
        h, m = map(int, t.split(':'))
        return h * 60 + m

    def min_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"

    # Convert all constraints to minutes since 9:00 AM
    constraintsConvert = {}
    for name, constr in constraints.items():
        start = time_to_min(constr["start"])
        end = time_to_min(constr["end"])
        constraintsConvert[name] = {
            "start": start,
            "end": end,
            "location": constr["location"],
            "duration": constr["duration"],
        }

    locations = ["EB", "GGP", "HA", "BV", "PR", "FD"]

    # Generate possible meeting times for each person
    possible_meetings = {}

    for person in constraintsConvert:
        person_constraints = constraintsConvert[person]
        possible_meetings[person] = []
        for loc in locations:
            if loc == person_constraints["location"]:
                continue
            travel_time = travel_times[f"{loc} to {person_constraints['location']}"]
            earliest_meet = person_constraints["start"] + travel_time
            latest_meet = person_constraints["end"] - person_constraints["duration"]
            for t in range(person_constraints["start"], person_constraints["end"] + 1):
                if t >= earliest_meet and t <= latest_meet:
                    possible_meetings[person].append({
                        "location": person_constraints["location"],
                        "start": t,
                        "end": t + person_constraints["duration"],
                    })

    # Now, try to find a schedule that includes as many meetings as possible without overlapping
    # This is a simplified version, as actually solving this would require backtracking
    # For the purpose of this example, we'll choose the first possible meetings

    # Filter possible meetings to only those where the user can attend
    possible_meetings_filtered = {}
    for person in possible_meetings:
        possible_meetings_filtered[person] = []
        for meeting in possible_meetings[person]:
            if meeting["start"] >= start_time:
                possible_meetings_filtered[person].append(meeting)

    # Now, try to find a combination of meetings that doesn't overlap
    # This is a simplified approach, as it's complex to implement a full scheduling algorithm
    # For the purpose of this example, we'll select the earliest possible meetings

    # Sort people by their earliest possible meeting time
    people_order = sorted(possible_meetings_filtered.keys(), key=lambda x: min(possible_meetings_filtered[x], key=lambda y: y["start"])["start"])

    selected_meetings = {}

    # Try to schedule each person in order of their earliest possible meeting
    for person in people_order:
        possible_meetings_person = possible_meetings_filtered[person]
        if not possible_meetings_person:
            continue
        # Find the earliest possible meeting that doesn't overlap with current_time
        for meeting in possible_meetings_person:
            if meeting["start"] >= current_time:
                selected_meetings[person] = meeting
                current_time = meeting["end"]
                break
        else:
            continue  # No meeting could be scheduled, skip this person

    # Now, sort the selected meetings by start time
    sorted_meetings = sorted(selected_meetings.values(), key=lambda x: x["start"])

    # Create the itinerary
    itinerary = []
    current_time = start_time
    for meeting in sorted_meetings:
        if meeting["start"] < current_time:
            # Adjust to the latest possible start time
            meeting["start"] = current_time
            meeting["end"] = current_time + meeting["duration"]
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": meeting["start"],
            "end_time": meeting["end"],
        })
        current_time = meeting["end"]

    return itinerary

# Run the computation
itinerary = compute_schedule()

# Convert times to 24-hour format with leading zeros if necessary
for i in range(len(itinerary)):
    meeting = itinerary[i]
    meeting["start_time"] = f"{meeting['start_time'].hour:02d}:{meeting['start_time'].minute:02d}"
    meeting["end_time"] = f"{meeting['end_time'].hour:02d}:{meeting['end_time'].minute:02d}"

# Prepare the JSON output
output = {
    "itinerary": itinerary
}

# Print the JSON output
print(json.dumps(output))