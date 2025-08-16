from z3 import *
import json

# Define friends with their meeting requirements,
# available time windows (in minutes after midnight),
# and the minimum meeting durations.
# Times:  09:00 = 540, 07:15 = 435, 11:45 = 705, 12:00 = 720, 12:15 = 735,
#         14:00 = 840, 15:00 = 900, 14:45 = 885, 19:00 = 1140,
#         18:30 = 1110, 21:30 = 1290, 22:30 = 1350.
friends = [
    {"name": "Karen",    "location": "The Castro",         "avail_start": 435,  "avail_end": 840,  "duration": 75},
    {"name": "Laura",    "location": "Fisherman's Wharf",  "avail_start": 705,  "avail_end": 1290, "duration": 60},
    {"name": "Deborah",  "location": "Alamo Square",       "avail_start": 720,  "avail_end": 900,  "duration": 105},
    {"name": "Elizabeth","location": "Chinatown",          "avail_start": 735,  "avail_end": 1290, "duration": 75},
    {"name": "Jason",    "location": "North Beach",        "avail_start": 885,  "avail_end": 1140, "duration": 90},
    {"name": "Steven",   "location": "Russian Hill",       "avail_start": 885,  "avail_end": 1110, "duration": 120},
    {"name": "Carol",    "location": "Haight-Ashbury",     "avail_start": 1290, "avail_end": 1350, "duration": 60}
]

# Travel distances in minutes between locations;
# each key is a pair (source, destination). Note that the values are not fully symmetric.
travel = {
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Russian Hill"): 19,

    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,

    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Russian Hill"): 7,

    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Russian Hill"): 18,

    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Russian Hill"): 7,

    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Russian Hill"): 13,

    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Russian Hill"): 4,

    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5
}

# Our starting point: Golden Gate Park at 09:00 (540 minutes)
start_time_GGP = 540
start_location = "Golden Gate Park"

# Create a Z3 solver instance.
s = Solver()

# Create an integer variable for each friend representing the meeting start time (in minutes after midnight)
meeting_vars = {}
for f in friends:
    meeting_vars[f["name"]] = Int(f"{f['name']}_start")

# Add constraints for each meeting:
#  1. The meeting must start no earlier than the friend’s availability.
#  2. The meeting (taking the minimum duration) must finish before the friend’s availability ends.
#  3. Even if a friend is not the very first meeting, a lower bound derived from the travel from Golden Gate Park holds.
for f in friends:
    name = f["name"]
    loc = f["location"]
    dur = f["duration"]
    avail_start = f["avail_start"]
    avail_end = f["avail_end"]
    s.add(meeting_vars[name] >= avail_start)
    s.add(meeting_vars[name] + dur <= avail_end)
    # Lower bound from starting at Golden Gate Park:
    if (start_location, loc) in travel:
        s.add(meeting_vars[name] >= start_time_GGP + travel[(start_location, loc)])

# Define a helper function for travel time lookup.
def get_travel_time(src, dst):
    return travel.get((src, dst), 1000)

# For every pair of meetings, ensure that one is scheduled after the other.
# That is, for two meetings i and j (with durations d_i and d_j), either
# meeting i finishes and then (plus travel time from i’s location to j’s location)
# is before meeting j starts,
# or vice‐versa.
names = [f["name"] for f in friends]
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        name_i = names[i]
        name_j = names[j]
        friend_i = next(x for x in friends if x["name"] == name_i)
        friend_j = next(x for x in friends if x["name"] == name_j)
        dur_i = friend_i["duration"]
        dur_j = friend_j["duration"]
        loc_i = friend_i["location"]
        loc_j = friend_j["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        s.add(Or(meeting_vars[name_i] + dur_i + travel_i_j <= meeting_vars[name_j],
                 meeting_vars[name_j] + dur_j + travel_j_i <= meeting_vars[name_i]))

# Check if a solution satisfying all constraints exists.
if s.check() == sat:
    m = s.model()
    schedule = []
    for f in friends:
        st = m[meeting_vars[f["name"]]].as_long()  # start time for friend f
        ft = st + f["duration"]                   # finish time = start + duration
        schedule.append({
            "person": f["name"],
            "location": f["location"],
            "start": st,
            "finish": ft
        })
    # Sort the meetings in order of start time.
    schedule.sort(key=lambda x: x["start"])
    
    # Helper function to convert minutes to "HH:MM" string.
    def format_time(t):
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"
    
    itinerary = []
    for entry in schedule:
        itinerary.append({
            "action": "meet",
            "person": entry["person"],
            "start_time": format_time(entry["start"]),
            "end_time": format_time(entry["finish"])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")