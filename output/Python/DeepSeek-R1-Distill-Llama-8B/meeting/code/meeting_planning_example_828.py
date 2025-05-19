# Read input travel times
travel_times = {
    # From Marina District (MD)
    "MD": {
        "Richmond District (RD)": 11,
        "Union Square (US)": 16,
        "Nob Hill (NH)": 12,
        "Fisherman's Wharf (FW)": 10,
        "Golden Gate Park (GGP)": 18,
        "Embarcadero (EB)": 14,
        "Financial District (FD)": 17,
        "North Beach (NB)": 11,
        "Presidio (PR)": 10,
    },
    # From Richmond District (RD)
    "RD": {
        "Marina District (MD)": 9,
        "Union Square (US)": 20,
        "Nob Hill (NH)": 17,
        "Fisherman's Wharf (FW)": 18,
        "Golden Gate Park (GGP)": 9,
        "Embarcadero (EB)": 19,
        "Financial District (FD)": 22,
        "North Beach (NB)": 17,
        "Presidio (PR)": 7,
    },
    # From Union Square (US)
    "US": {
        "Marina District (MD)": 18,
        "Richmond District (RD)": 20,
        "Nob Hill (NH)": 9,
        "Fisherman's Wharf (FW)": 15,
        "Golden Gate Park (GGP)": 22,
        "Embarcadero (EB)": 11,
        "Financial District (FD)": 9,
        "North Beach (NB)": 10,
        "Presidio (PR)": 24,
    },
    # From Nob Hill (NH)
    "NH": {
        "Marina District (MD)": 11,
        "Richmond District (RD)": 14,
        "Union Square (US)": 7,
        "Fisherman's Wharf (FW)": 10,
        "Golden Gate Park (GGP)": 17,
        "Embarcadero (EB)": 9,
        "Financial District (FD)": 9,
        "North Beach (NB)": 8,
        "Presidio (PR)": 17,
    },
    # From Fisherman's Wharf (FW)
    "FW": {
        "Marina District (MD)": 9,
        "Richmond District (RD)": 18,
        "Union Square (US)": 13,
        "Nob Hill (NH)": 11,
        "Golden Gate Park (GGP)": 25,
        "Embarcadero (EB)": 8,
        "Financial District (FD)": 11,
        "North Beach (NB)": 6,
        "Presidio (PR)": 17,
    },
    # From Golden Gate Park (GGP)
    "GGP": {
        "Marina District (MD)": 16,
        "Richmond District (RD)": 7,
        "Union Square (US)": 22,
        "Nob Hill (NH)": 20,
        "Fisherman's Wharf (FW)": 24,
        "Embarcadero (EB)": 25,
        "Financial District (FD)": 26,
        "North Beach (NB)": 23,
        "Presidio (PR)": 11,
    },
    # From Embarcadero (EB)
    "EB": {
        "Marina District (MD)": 12,
        "Richmond District (RD)": 21,
        "Union Square (US)": 10,
        "Nob Hill (NH)": 10,
        "Fisherman's Wharf (FW)": 6,
        "Golden Gate Park (GGP)": 25,
        "Financial District (FD)": 4,
        "North Beach (NB)": 5,
        "Presidio (PR)": 20,
    },
    # From Financial District (FD)
    "FD": {
        "Marina District (MD)": 15,
        "Richmond District (RD)": 21,
        "Union Square (US)": 9,
        "Nob Hill (NH)": 8,
        "Fisherman's Wharf (FW)": 10,
        "Golden Gate Park (GGP)": 23,
        "Embarcadero (EB)": 4,
        "North Beach (NB)": 7,
        "Presidio (PR)": 22,
    },
    # From North Beach (NB)
    "NB": {
        "Marina District (MD)": 9,
        "Richmond District (RD)": 18,
        "Union Square (US)": 7,
        "Nob Hill (NH)": 7,
        "Fisherman's Wharf (FW)": 5,
        "Golden Gate Park (GGP)": 22,
        "Embarcadero (EB)": 6,
        "Financial District (FD)": 8,
        "Presidio (PR)": 17,
    },
    # From Presidio (PR)
    "PR": {
        "Marina District (MD)": 11,
        "Richmond District (RD)": 7,
        "Union Square (US)": 22,
        "Nob Hill (NH)": 18,
        "Fisherman's Wharf (FW)": 19,
        "Golden Gate Park (GGP)": 12,
        "Embarcadero (EB)": 20,
        "Financial District (FD)": 23,
        "North Beach (NB)": 18,
    },
}

# Read constraints
constraints = {
    "Stephanie": {
        "start": "16:15",
        "end": "21:30",
        "location": "Richmond District (RD)",
        "duration": 75,
    },
    "William": {
        "start": "10:45",
        "end": "17:30",
        "location": "Union Square (US)",
        "duration": 45,
    },
    "Elizabeth": {
        "start": "12:15",
        "end": "15:00",
        "location": "Nob Hill (NH)",
        "duration": 105,
    },
    "Joseph": {
        "start": "12:45",
        "end": "14:00",
        "location": "Fisherman's Wharf (FW)",
        "duration": 75,
    },
    "Anthony": {
        "start": "13:00",
        "end": "20:30",
        "location": "Golden Gate Park (GGP)",
        "duration": 75,
    },
    "Barbara": {
        "start": "19:15",
        "end": "20:30",
        "location": "Embarcadero (EB)",
        "duration": 75,
    },
    "Carol": {
        "start": "11:45",
        "end": "16:15",
        "location": "Financial District (FD)",
        "duration": 60,
    },
    "Sandra": {
        "start": "10:00",
        "end": "12:30",
        "location": "North Beach (NB)",
        "duration": 15,
    },
    "Kenneth": {
        "start": "21:15",
        "end": "22:15",
        "location": "Presidio (PR)",
        "duration": 45,
    },
}

# Starting location is Marina District (MD) at 9:00 AM
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

    locations = ["MD", "RD", "US", "NH", "FW", "GGP", "EB", "FD", "NB", "PR"]

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