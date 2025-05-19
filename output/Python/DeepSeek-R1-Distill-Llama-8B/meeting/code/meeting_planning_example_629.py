# Read input travel times
travel_times = {
    # From Russian Hill (RH)
    "RH": {
        "Presidio (PR)": 14,
        "Chinatown (CT)": 9,
        "Pacific Heights (PH)": 7,
        "Richmond District (RD)": 14,
        "Fisherman's Wharf (FW)": 7,
        "Golden Gate Park (GGP)": 21,
        "Bayview (BV)": 23,
    },
    # From Presidio (PR)
    "PR": {
        "Russian Hill (RH)": 14,
        "Chinatown (CT)": 21,
        "Pacific Heights (PH)": 11,
        "Richmond District (RD)": 7,
        "Fisherman's Wharf (FW)": 19,
        "Golden Gate Park (GGP)": 12,
        "Bayview (BV)": 31,
    },
    # From Chinatown (CT)
    "CT": {
        "Russian Hill (RH)": 7,
        "Presidio (PR)": 19,
        "Pacific Heights (PH)": 11,
        "Richmond District (RD)": 20,
        "Fisherman's Wharf (FW)": 8,
        "Golden Gate Park (GGP)": 23,
        "Bayview (BV)": 22,
    },
    # From Pacific Heights (PH)
    "PH": {
        "Russian Hill (RH)": 7,
        "Presidio (PR)": 11,
        "Chinatown (CT)": 11,
        "Richmond District (RD)": 12,
        "Fisherman's Wharf (FW)": 13,
        "Golden Gate Park (GGP)": 15,
        "Bayview (BV)": 23,
    },
    # From Richmond District (RD)
    "RD": {
        "Russian Hill (RH)": 13,
        "Presidio (PR)": 7,
        "Chinatown (CT)": 20,
        "Pacific Heights (PH)": 10,
        "Fisherman's Wharf (FW)": 18,
        "Golden Gate Park (GGP)": 9,
        "Bayview (BV)": 25,
    },
    # From Fisherman's Wharf (FW)
    "FW": {
        "Russian Hill (RH)": 7,
        "Presidio (PR)": 17,
        "Chinatown (CT)": 12,
        "Pacific Heights (PH)": 12,
        "Richmond District (RD)": 18,
        "Golden Gate Park (GGP)": 24,
        "Bayview (BV)": 25,
    },
    # From Golden Gate Park (GGP)
    "GGP": {
        "Russian Hill (RH)": 19,
        "Presidio (PR)": 11,
        "Chinatown (CT)": 23,
        "Pacific Heights (PH)": 16,
        "Richmond District (RD)": 7,
        "Fisherman's Wharf (FW)": 24,
        "Bayview (BV)": 22,
    },
    # From Bayview (BV)
    "BV": {
        "Russian Hill (RH)": 23,
        "Presidio (PR)": 31,
        "Chinatown (CT)": 18,
        "Pacific Heights (PH)": 23,
        "Richmond District (RD)": 25,
        "Fisherman's Wharf (FW)": 25,
        "Golden Gate Park (GGP)": 22,
    },
}

# Read constraints
constraints = {
    "Matthew": {
        "start": "11:00",
        "end": "21:00",
        "location": "Presidio (PR)",
        "duration": 90,
    },
    "Margaret": {
        "start": "9:15",
        "end": "18:45",
        "location": "Chinatown (CT)",
        "duration": 90,
    },
    "Nancy": {
        "start": "14:15",
        "end": "17:00",
        "location": "Pacific Heights (PH)",
        "duration": 15,
    },
    "Helen": {
        "start": "19:45",
        "end": "22:00",
        "location": "Richmond District (RD)",
        "duration": 60,
    },
    "Rebecca": {
        "start": "21:15",
        "end": "22:15",
        "location": "Fisherman's Wharf (FW)",
        "duration": 60,
    },
    "Kimberly": {
        "start": "13:00",
        "end": "16:30",
        "location": "Golden Gate Park (GGP)",
        "duration": 120,
    },
    "Kenneth": {
        "start": "14:30",
        "end": "18:00",
        "location": "Bayview (BV)",
        "duration": 60,
    },
}

# Starting location is Russian Hill (RH) at 9:00 AM
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

    locations = ["RH", "PR", "CT", "PH", "RD", "FW", "GGP", "BV"]

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