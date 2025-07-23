# Define the start time
start_time = 540  # 9:00 AM

# Define the travel times
travel_times = {
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Richmond District", "Bayview"): 26,
    ("Bayview", "Fisherman's Wharf"): 26,
    ("Fisherman's Wharf", "Mission District"): 15,
}

# Define the meetings
meetings = {
    "Mary": {"start": 1300, "end": 1395, "location": "Richmond District"},
    "Thomas": {"start": 1515, "end": 1815, "location": "Bayview"},
    "Sarah": {"start": 1841, "end": 1946, "location": "Fisherman's Wharf"},
    "Helen": {"start": 2145, "end": 2175, "location": "Mission District"},
}

# Create the itinerary
itinerary = []
current_time = start_time

# Add the meetings in the order they are scheduled
for name, details in meetings.items():
    # Travel to the location of the next meeting
    if itinerary:
        current_time += travel_times[(itinerary[-1]["location"], details["location"])]
    else:
        current_time += travel_times[("Haight-Ashbury", details["location"])]
    # Ensure the meeting starts after the travel time
    if current_time < details["start"]:
        current_time = details["start"]
    # Add the meeting to the itinerary
    itinerary.append({
        "action": "meet",
        "person": name,
        "start_time": f"{current_time // 60:02}:{current_time % 60:02}",
        "end_time": f"{details['end'] // 60:02}:{details['end'] % 60:02}"
    })
    # Update the current time to the end of the meeting
    current_time = details["end"]

# Print the itinerary
print({"itinerary": itinerary})