# Read input travel times
travel_times = {
    # From Golden Gate Park (GGP)
    "GGP": {
        "Fisherman's Wharf (FW)": 24,
        "Bayview (BV)": 23,
        "Mission District (MD)": 17,
        "Embarcadero (EB)": 25,
        "Financial District (FD)": 26,
    },
    # From Fisherman's Wharf (FW)
    "FW": {
        "GGP": 25,
        "Bayview (BV)": 26,
        "Mission District (MD)": 22,
        "Embarcadero (EB)": 8,
        "Financial District (FD)": 11,
    },
    # From Bayview (BV)
    "BV": {
        "GGP": 22,
        "FW": 25,
        "Mission District (MD)": 13,
        "Embarcadero (EB)": 19,
        "Financial District (FD)": 19,
    },
    # From Mission District (MD)
    "MD": {
        "GGP": 17,
        "FW": 22,
        "Bayview (BV)": 15,
        "Embarcadero (EB)": 19,
        "Financial District (FD)": 17,
    },
    # From Embarcadero (EB)
    "EB": {
        "GGP": 25,
        "FW": 6,
        "Bayview (BV)": 21,
        "Mission District (MD)": 20,
        "Financial District (FD)": 4,
    },
    # From Financial District (FD)
    "FD": {
        "GGP": 23,
        "FW": 10,
        "Bayview (BV)": 19,
        "Mission District (MD)": 17,
        "Embarcadero (EB)": 4,
    },
}

# Read constraints
constraints = {
    "Joseph": {
        "start": "8:00",
        "end": "17:30",
        "location": "Fisherman's Wharf (FW)",
        "duration": 90,
    },
    "Jeffrey": {
        "start": "17:30",
        "end": "21:30",
        "location": "Bayview (BV)",
        "duration": 60,
    },
    "Kevin": {
        "start": "11:15",
        "end": "14:15",
        "location": "Mission District (MD)",
        "duration": 30,
    },
    "David": {
        "start": "8:15",
        "end": "9:00",
        "location": "Embarcadero (EB)",
        "duration": 30,
    },
    "Barbara": {
        "start": "10:30",
        "end": "16:30",
        "location": "Financial District (FD)",
        "duration": 15,
    },
}

# Starting location is Golden Gate Park (GGP) at 9:00 AM
start_time = "9:00"

def compute_schedule():
    from copy import deepcopy
    from datetime import datetime, timedelta
    import itertools

    # Convert times to minutes since 9:00 AM
    def time_to_min(t):
        h, m = map(int, t.split(':'))
        return h * 60 + m

    def min_to_time(m):
        return f"{(m // 60):02d}:{m % 60:02d}"

    # Convert all times to minutes since 9:00 AM
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

    locations = ["GGP", "FW", "BV", "MD", "EB", "FD"]

    # Generate possible meeting times for each person
    all_people = ["Joseph", "Jeffrey", "Kevin", "David", "Barbara"]
    possible_meetings = {}

    for person in all_people:
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

    # Selecting the earliest possible meetings
    selected_meetings = {}

    # Barbara
    for meeting in possible_meetings_filtered["Barbara"]:
        if meeting["start"] >= start_time and (not selected_meetings or
           (meeting["start"] >= selected_meetings[-1]["end"] + 1)):
            selected_meetings["Barbara"] = meeting
            break

    # Kevin
    for meeting in possible_meetings_filtered["Kevin"]:
        if meeting["start"] >= start_time and (not selected_meetings or
           (meeting["start"] >= selected_meetings[-1]["end"] + 1)):
            selected_meetings["Kevin"] = meeting
            break

    # Joseph
    for meeting in possible_meetings_filtered["Joseph"]:
        if meeting["start"] >= start_time and (not selected_meetings or
           (meeting["start"] >= selected_meetings[-1]["end"] + 1)):
            selected_meetings["Joseph"] = meeting
            break

    # Jeffrey
    for meeting in possible_meetings_filtered["Jeffrey"]:
        if meeting["start"] >= start_time and (not selected_meetings or
           (meeting["start"] >= selected_meetings[-1]["end"] + 1)):
            selected_meetings["Jeffrey"] = meeting
            break

    # David
    for meeting in possible_meetings_filtered["David"]:
        if meeting["start"] >= start_time and (not selected_meetings or
           (meeting["start"] >= selected_meetings[-1]["end"] + 1)):
            selected_meetings["David"] = meeting
            break

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