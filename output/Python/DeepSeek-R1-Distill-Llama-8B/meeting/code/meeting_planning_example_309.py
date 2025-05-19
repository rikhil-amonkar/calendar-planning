# Read input travel times
travel_times = {
    # From Financial District (FD)
    "FD": {
        "Chinatown (CT)": 5,
        "Alamo Square (AS)": 17,
        "Bayview (BV)": 19,
        "Fisherman's Wharf (FW)": 10,
    },
    # From Chinatown (CT)
    "CT": {
        "FD": 5,
        "AS": 17,
        "BV": 22,
        "FW": 8,
    },
    # From Alamo Square (AS)
    "AS": {
        "FD": 17,
        "CT": 16,
        "BV": 16,
        "FW": 19,
    },
    # From Bayview (BV)
    "BV": {
        "FD": 19,
        "CT": 18,
        "AS": 16,
        "FW": 25,
    },
    # From Fisherman's Wharf (FW)
    "FW": {
        "FD": 11,
        "CT": 12,
        "AS": 20,
        "BV": 26,
    },
}

# Read constraints
constraints = {
    "Nancy": {
        "start": "9:30",
        "end": "13:30",
        "location": "Chinatown (CT)",
        "duration": 90,
    },
    "Mary": {
        "start": "7:00",
        "end": "21:00",
        "location": "Alamo Square (AS)",
        "duration": 75,
    },
    "Jessica": {
        "start": "11:15",
        "end": "13:45",
        "location": "Bayview (BV)",
        "duration": 45,
    },
    "Rebecca": {
        "start": "7:00",
        "end": "8:30",
        "location": "Fisherman's Wharf (FW)",
        "duration": 45,
    },
}

# Starting location is Financial District (FD) at 9:00 AM
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

    locations = ["FD", "CT", "AS", "BV", "FW"]

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

    # Rebecca is only available until 8:30 AM, so she must be scheduled first
    if "Rebecca" in possible_meetings_filtered and possible_meetings_filtered["Rebecca"]:
        earliest_rebecca = min(possible_meetings_filtered["Rebecca"], key=lambda x: x["start"])
        selected_meetings["Rebecca"] = earliest_rebecca
        current_time = earliest_rebecca["end"]

    # Now, check for other meetings that can be scheduled after Rebecca
    selected_meetings = {}
    selected_meetings["Rebecca"] = None

    # Sort the remaining people by their earliest possible meeting time
    remaining_people = [person for person in possible_meetings_filtered if person != "Rebecca"]
    remaining_people.sort(key=lambda x: min(possible_meetings_filtered[x], key=lambda y: y["start"])["start"])

    # Try to schedule each person in order of their earliest possible meeting
    for person in remaining_people:
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