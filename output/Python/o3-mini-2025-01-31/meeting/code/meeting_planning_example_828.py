#!/usr/bin/env python3
import json

# Helper functions for time conversion (all times in minutes from midnight)
def time_to_minutes(t):
    # t is a string in "H:MM" 24-hour format, e.g., "9:00" or "13:30"
    parts = t.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    # Format without leading zero for hour, but always 2-digit minute
    return f"{hour}:{minute:02d}"

# Travel times dictionary (from_location, to_location): minutes
travel_times = {
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Presidio"): 10,

    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Presidio"): 7,

    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,

    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Presidio"): 17,

    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Presidio"): 17,

    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Presidio"): 11,

    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,

    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Presidio"): 22,

    ("North Beach", "Marina District"): 9,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Presidio"): 17,

    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18
}

# Meeting constraints data: each meeting as a dictionary
meetings = [
    {
        "person": "Stephanie",
        "location": "Richmond District",
        "available_start": time_to_minutes("16:15"),
        "available_end": time_to_minutes("21:30"),
        "min_duration": 75
    },
    {
        "person": "William",
        "location": "Union Square",
        "available_start": time_to_minutes("10:45"),
        "available_end": time_to_minutes("17:30"),
        "min_duration": 45
    },
    {
        "person": "Elizabeth",
        "location": "Nob Hill",
        "available_start": time_to_minutes("12:15"),
        "available_end": time_to_minutes("15:00"),
        "min_duration": 105
    },
    {
        "person": "Joseph",
        "location": "Fisherman's Wharf",
        "available_start": time_to_minutes("12:45"),
        "available_end": time_to_minutes("14:00"),
        "min_duration": 75
    },
    {
        "person": "Anthony",
        "location": "Golden Gate Park",
        "available_start": time_to_minutes("13:00"),
        "available_end": time_to_minutes("20:30"),
        "min_duration": 75
    },
    {
        "person": "Barbara",
        "location": "Embarcadero",
        "available_start": time_to_minutes("19:15"),
        "available_end": time_to_minutes("20:30"),
        "min_duration": 75
    },
    {
        "person": "Carol",
        "location": "Financial District",
        "available_start": time_to_minutes("11:45"),
        "available_end": time_to_minutes("16:15"),
        "min_duration": 60
    },
    {
        "person": "Sandra",
        "location": "North Beach",
        "available_start": time_to_minutes("10:00"),
        "available_end": time_to_minutes("12:30"),
        "min_duration": 15
    },
    {
        "person": "Kenneth",
        "location": "Presidio",
        "available_start": time_to_minutes("21:15"),
        "available_end": time_to_minutes("22:15"),
        "min_duration": 45
    }
]

# We start at Marina District at 9:00
current_location = "Marina District"
current_time = time_to_minutes("9:00")

# We will compute a schedule that tries to meet as many friends as possible.
# For this example, we choose an order that satisfies the constraints and computed travel times:
# Order chosen: Sandra, William, Elizabeth, Carol, Anthony, Stephanie, Barbara, Kenneth
# (Joseph is skipped because of time conflicts with Elizabeth)

itinerary = []

# 1. Sandra at North Beach
travel = travel_times[(current_location, "North Beach")]
current_time += travel  # travel time from Marina to North Beach
# Wait until available start if arrived early
if current_time < meetings[7]["available_start"]:
    current_time = meetings[7]["available_start"]
start_time = current_time
end_time = start_time + meetings[7]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": "North Beach",
    "person": "Sandra",
    "start_time": minutes_to_time(start_time),
    "end_time": minutes_to_time(end_time)
})
# Update current location and time
current_location = "North Beach"
current_time = end_time

# 2. William at Union Square
travel = travel_times[(current_location, "Union Square")]
current_time += travel
if current_time < meetings[1]["available_start"]:
    current_time = meetings[1]["available_start"]
start_time = current_time
end_time = start_time + meetings[1]["min_duration"]
itinerary.append({
    "action": "meet",
    "location": "Union Square",
    "person": "William",
    "start_time": minutes_to_time(start_time),
    "end_time": minutes_to_time(end_time)
})
current_location = "Union Square"
current_time = end_time

# 3. Elizabeth at Nob Hill
travel = travel_times[(current_location, "Nob Hill")]
current_time += travel
if current_time < meetings[2]["available_start"]:
    current_time = meetings[2]["available_start"]
start_time = current_time
end_time = start_time + meetings[2]["min_duration"]
# Ensure meeting concludes by available_end (Elizabeth available_end is 15:00 i.e., 900 minutes)
if end_time > meetings[2]["available_end"]:
    end_time = meetings[2]["available_end"]
itinerary.append({
    "action": "meet",
    "location": "Nob Hill",
    "person": "Elizabeth",
    "start_time": minutes_to_time(start_time),
    "end_time": minutes_to_time(end_time)
})
current_location = "Nob Hill"
current_time = end_time

# 4. Carol at Financial District
travel = travel_times[(current_location, "Financial District")]
current_time += travel
if current_time < meetings[6]["available_start"]:
    current_time = meetings[6]["available_start"]
start_time = current_time
end_time = start_time + meetings[6]["min_duration"]
if end_time > meetings[6]["available_end"]:
    end_time = meetings[6]["available_end"]
itinerary.append({
    "action": "meet",
    "location": "Financial District",
    "person": "Carol",
    "start_time": minutes_to_time(start_time),
    "end_time": minutes_to_time(end_time)
})
current_location = "Financial District"
current_time = end_time

# 5. Anthony at Golden Gate Park
travel = travel_times[(current_location, "Golden Gate Park")]
current_time += travel
if current_time < meetings[4]["available_start"]:
    current_time = meetings[4]["available_start"]
start_time = current_time
end_time = start_time + meetings[4]["min_duration"]
if end_time > meetings[4]["available_end"]:
    end_time = meetings[4]["available_end"]
itinerary.append({
    "action": "meet",
    "location": "Golden Gate Park",
    "person": "Anthony",
    "start_time": minutes_to_time(start_time),
    "end_time": minutes_to_time(end_time)
})
current_location = "Golden Gate Park"
current_time = end_time

# 6. Stephanie at Richmond District
travel = travel_times[(current_location, "Richmond District")]
current_time += travel
if current_time < meetings[0]["available_start"]:
    current_time = meetings[0]["available_start"]
start_time = current_time
end_time = start_time + meetings[0]["min_duration"]
if end_time > meetings[0]["available_end"]:
    end_time = meetings[0]["available_end"]
itinerary.append({
    "action": "meet",
    "location": "Richmond District",
    "person": "Stephanie",
    "start_time": minutes_to_time(start_time),
    "end_time": minutes_to_time(end_time)
})
current_location = "Richmond District"
current_time = end_time

# 7. Barbara at Embarcadero
travel = travel_times[(current_location, "Embarcadero")]
current_time += travel
if current_time < meetings[5]["available_start"]:
    current_time = meetings[5]["available_start"]
start_time = current_time
end_time = start_time + meetings[5]["min_duration"]
if end_time > meetings[5]["available_end"]:
    end_time = meetings[5]["available_end"]
itinerary.append({
    "action": "meet",
    "location": "Embarcadero",
    "person": "Barbara",
    "start_time": minutes_to_time(start_time),
    "end_time": minutes_to_time(end_time)
})
current_location = "Embarcadero"
current_time = end_time

# 8. Kenneth at Presidio
travel = travel_times[(current_location, "Presidio")]
current_time += travel
if current_time < meetings[8]["available_start"]:
    current_time = meetings[8]["available_start"]
start_time = current_time
end_time = start_time + meetings[8]["min_duration"]
if end_time > meetings[8]["available_end"]:
    end_time = meetings[8]["available_end"]
itinerary.append({
    "action": "meet",
    "location": "Presidio",
    "person": "Kenneth",
    "start_time": minutes_to_time(start_time),
    "end_time": minutes_to_time(end_time)
})
current_location = "Presidio"
current_time = end_time

# Build the final schedule dictionary
schedule = {"itinerary": itinerary}

# Output the result in JSON format
print(json.dumps(schedule, indent=2))