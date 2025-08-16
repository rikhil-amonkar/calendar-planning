from z3 import Solver, Int, And, If, sat
import json

# We'll represent time in minutes from midnight.
# Helper function to convert minutes to "HH:MM" string.
def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Data for each friend meeting:
# Each meeting has:
#   - Person name
#   - Location (for travel purposes)
#   - available start and end (in minutes)
#   - minimum duration (in minutes)
#
# In our chosen ordering we will schedule (in order):
#   1. Laura at Richmond District: available 09:45 (585) to 18:00 (1080), duration 60.
#   2. Jeffrey at Fisherman's Wharf: available 10:15 (615) to 13:00 (780), duration 90.
#   3. Jason at Financial District: available 10:45 (645) to 16:00 (960), duration 105.
#   4. Richard at Chinatown: available 09:30 (570) to 21:00 (1260), duration 15.
#   5. Margaret at Embarcadero: available 13:15 (795) to 19:00 (1140), duration 90.
#   6. Melissa at Union Square: available 17:45 (1065) to 18:15 (1095), duration 15.
#   7. George at Golden Gate Park: available 19:00 (1140) to 22:00 (1320), duration 75.

# For our scheduling problem, we also have travel times.
# The starting location is Presidio at 09:00 (540).
# Travel times we use (in minutes) are given as follows:
#
# From Presidio to:
#   Richmond District: 7
#   Fisherman's Wharf: 19
#   Financial District: 23
#   Chinatown: 21
#   Embarcadero: 20
#   Union Square: 22
#   Golden Gate Park: 12
#
# And travel times between meeting locations (in our order):
#   Richmond District -> Fisherman's Wharf: 18
#   Fisherman's Wharf -> Financial District: 11
#   Financial District -> Chinatown: 5
#   Chinatown -> Embarcadero: 5
#   Embarcadero -> Union Square: 10
#   Union Square -> Golden Gate Park: 22

# Define the parameters for each meeting:
meets = [
    { "person": "Laura", "location": "Richmond District", "avail_start": 585, "avail_end": 1080, "duration": 60 },
    { "person": "Jeffrey", "location": "Fisherman's Wharf", "avail_start": 615, "avail_end": 780, "duration": 90 },
    { "person": "Jason", "location": "Financial District", "avail_start": 645, "avail_end": 960, "duration": 105 },
    { "person": "Richard", "location": "Chinatown", "avail_start": 570, "avail_end": 1260, "duration": 15 },
    { "person": "Margaret", "location": "Embarcadero", "avail_start": 795, "avail_end": 1140, "duration": 90 },
    { "person": "Melissa", "location": "Union Square", "avail_start": 1065, "avail_end": 1095, "duration": 15 },
    { "person": "George", "location": "Golden Gate Park", "avail_start": 1140, "avail_end": 1320, "duration": 75 }
]

# Predefined travel times (in minutes)
# From Presidio (start) to each meeting location:
travel_from_presidio = {
    "Richmond District": 7,
    "Fisherman's Wharf": 19,
    "Financial District": 23,
    "Chinatown": 21,
    "Embarcadero": 20,
    "Union Square": 22,
    "Golden Gate Park": 12
}
# Travel times between meetings (ordered as in our list):
travel_between = [
    # From meeting 0 (Laura at Richmond District) to meeting 1 (Jeffrey at Fisherman's Wharf)
    18,  
    # From meeting 1 (Jeffrey at Fisherman's Wharf) to meeting 2 (Jason at Financial District)
    11,  
    # From meeting 2 (Jason at Financial District) to meeting 3 (Richard at Chinatown)
    5,   
    # From meeting 3 (Richard at Chinatown) to meeting 4 (Margaret at Embarcadero)
    5,   
    # From meeting 4 (Margaret at Embarcadero) to meeting 5 (Melissa at Union Square)
    10,  
    # From meeting 5 (Melissa at Union Square) to meeting 6 (George at Golden Gate Park)
    22
]

# Create a Z3 solver instance
s = Solver()

# Create an integer variable for the start time of each meeting (in minutes since midnight).
start_vars = [Int(f"start_{i}") for i in range(len(meets))]

# For convenience, define end time as start + duration.
ends = [start_vars[i] + meets[i]["duration"] for i in range(len(meets))]

# Add constraints for each meeting's available time window:
for i, m in enumerate(meets):
    # Meeting must start no earlier than the friend’s available start and finish no later than available end.
    s.add(start_vars[i] >= m["avail_start"])
    s.add(ends[i] <= m["avail_end"])

# Add constraint for the first meeting: travel time from Presidio to that meeting's location.
first_travel = travel_from_presidio[meets[0]["location"]]
s.add(start_vars[0] >= 540 + first_travel)  # 540 = 09:00

# Add constraints for meetings in sequence:
for i in range(1, len(meets)):
    # Travel time from previous meeting to current one.
    travel_time = travel_between[i-1]
    s.add(start_vars[i] >= ends[i-1] + travel_time)

# (Optional) We can try to “minimize” the slack time before each meeting.
# For our purposes we are simply looking for a feasible schedule.

if s.check() == sat:
    m = s.model()
    # Extract meeting times:
    itinerary = []
    for i, meet_def in enumerate(meets):
        start_min = m[start_vars[i]].as_long()
        end_min = start_min + meet_def["duration"]
        itinerary.append({
            "action": "meet",
            "person": meet_def["person"],
            "start_time": min_to_time(start_min),
            "end_time": min_to_time(end_min)
        })

    # For meetings that involve waiting for the friend to become available,
    # our constraints force the meeting to start no earlier than the available start.
    # Also, if travel would allow earlier arrival, we wait until the available time.
    
    # Now, print the final itinerary in JSON format:
    output = {"itinerary": itinerary}
    # For clarity, pretty-print the JSON:
    print(json.dumps(output, indent=2))
else:
    print("No feasible schedule found")