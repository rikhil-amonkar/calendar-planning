from z3 import *
import json

# Travel times (in minutes) between locations.
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
    ("Russian Hill", "North Beach"): 5,
}

# Data for each friend:
# Times are in minutes from midnight.
# Carol: 21:30-22:30, min meeting 60.
# Laura: 11:45-21:30, min meeting 60.
# Karen: 7:15-14:00, min meeting 75.
# Elizabeth: 12:15-21:30, min meeting 75.
# Deborah: 12:00-15:00, min meeting 105.
# Jason: 14:45-19:00, min meeting 90.
# Steven: 14:45-18:30, min meeting 120.
friends_data = [
    {"name": "Carol", "location": "Haight-Ashbury", "avail_start": 1290, "avail_end": 1350, "min_duration": 60},
    {"name": "Laura", "location": "Fisherman's Wharf", "avail_start": 705, "avail_end": 1290, "min_duration": 60},
    {"name": "Karen", "location": "The Castro", "avail_start": 435, "avail_end": 840, "min_duration": 75},
    {"name": "Elizabeth", "location": "Chinatown", "avail_start": 735, "avail_end": 1290, "min_duration": 75},
    {"name": "Deborah", "location": "Alamo Square", "avail_start": 720, "avail_end": 900, "min_duration": 105},
    {"name": "Jason", "location": "North Beach", "avail_start": 885, "avail_end": 1140, "min_duration": 90},
    {"name": "Steven", "location": "Russian Hill", "avail_start": 885, "avail_end": 1110, "min_duration": 120},
]

# You arrive at Golden Gate Park at 9:00AM (540 minutes from midnight)
start_location = "Golden Gate Park"
arrival_time = 540

# Create an Optimize object
opt = Optimize()

# Create decision variables for each friend:
# - meet: Bool variable indicating if we meet the friend.
# - start: meeting start time (in minutes from midnight)
# - end: meeting end time (set to start + min_duration if meeting occurs)
# - order: integer indicating the order in which the meeting happens (0 if not scheduled)
meeting_vars = {}
for friend in friends_data:
    f = friend["name"]
    meeting_vars[f] = {
        "meet": Bool(f"meet_{f}"),
        "start": Int(f"start_{f}"),
        "end": Int(f"end_{f}"),
        "order": Int(f"order_{f}"),
    }

# For each friend, add constraints based on whether we schedule the meeting.
for friend in friends_data:
    f = friend["name"]
    loc = friend["location"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    dur = friend["min_duration"]
    # If meeting is scheduled, the meeting must fall entirely within the availability window,
    # and the meeting duration is exactly the required minimum.
    # Also the order variable is between 1 and 7. Otherwise, set start, end, order to 0.
    opt.add(
        If(
            meeting_vars[f]["meet"],
            And(
                meeting_vars[f]["start"] >= a_start,
                meeting_vars[f]["start"] + dur <= a_end,
                meeting_vars[f]["end"] == meeting_vars[f]["start"] + dur,
                meeting_vars[f]["order"] >= 1,
                meeting_vars[f]["order"] <= 7
            ),
            And(
                meeting_vars[f]["start"] == 0,
                meeting_vars[f]["end"] == 0,
                meeting_vars[f]["order"] == 0
            )
        )
    )
    # Ensure meeting times (if scheduled) are within a valid daily range.
    opt.add(If(meeting_vars[f]["meet"], And(meeting_vars[f]["start"] >= 0, meeting_vars[f]["end"] <= 1440), True))

# For the first meeting, we must travel from Golden Gate Park.
# If a friend is scheduled with order == 1, then meeting start time must be at least
# arrival_time plus travel time from Golden Gate Park to that friend's location.
for friend in friends_data:
    f = friend["name"]
    loc = friend["location"]
    travel_time_first = travel[(start_location, loc)]
    opt.add(
        Implies(
            And(meeting_vars[f]["meet"], meeting_vars[f]["order"] == 1),
            meeting_vars[f]["start"] >= arrival_time + travel_time_first
        )
    )

# For any two scheduled meetings, enforce ordering and travel constraints.
for i in range(len(friends_data)):
    for j in range(i + 1, len(friends_data)):
        f1 = friends_data[i]["name"]
        f2 = friends_data[j]["name"]
        loc1 = friends_data[i]["location"]
        loc2 = friends_data[j]["location"]
        # If both meetings are scheduled, their order numbers must be different.
        opt.add(
            Implies(
                And(meeting_vars[f1]["meet"], meeting_vars[f2]["meet"]),
                meeting_vars[f1]["order"] != meeting_vars[f2]["order"]
            )
        )
        # If f1 comes before f2 then ensure enough time to travel from f1 location to f2 location.
        opt.add(
            Implies(
                And(meeting_vars[f1]["meet"], meeting_vars[f2]["meet"], meeting_vars[f1]["order"] < meeting_vars[f2]["order"]),
                meeting_vars[f1]["end"] + travel[(loc1, loc2)] <= meeting_vars[f2]["start"]
            )
        )
        # Also enforce the converse ordering constraint.
        opt.add(
            Implies(
                And(meeting_vars[f1]["meet"], meeting_vars[f2]["meet"], meeting_vars[f2]["order"] < meeting_vars[f1]["order"]),
                meeting_vars[f2]["end"] + travel[(loc2, loc1)] <= meeting_vars[f1]["start"]
            )
        )

# Objective: maximize the number of meetings scheduled.
num_meetings = Sum([If(meeting_vars[f]["meet"], 1, 0) for f in meeting_vars])
opt.maximize(num_meetings)

# Check the optimization and extract the model.
if opt.check() == sat:
    m = opt.model()
else:
    m = None

# Build the itinerary from the model.
itinerary = []
if m:
    for friend in friends_data:
        f = friend["name"]
        if m.evaluate(meeting_vars[f]["meet"]):
            order_val = m.evaluate(meeting_vars[f]["order"]).as_long()
            start_val = m.evaluate(meeting_vars[f]["start"]).as_long()
            end_val = m.evaluate(meeting_vars[f]["end"]).as_long()
            itinerary.append((order_val, f, friend["location"], start_val, end_val))
    # Sort the itinerary based on the meeting order.
    itinerary.sort(key=lambda x: x[0])

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

result = {"itinerary": []}
for order_val, person, location, start_val, end_val in itinerary:
    result["itinerary"].append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": format_time(start_val),
        "end_time": format_time(end_val)
    })

# Output the result as JSON.
print(json.dumps(result))