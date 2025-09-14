from z3 import *
import json

def format_time(m):
    # Format minutes from midnight as H:MM in 24-hour format (no leading zero for hour)
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

# Define the friends with their meeting details
friends = [
    {"name": "Amanda", "location": "Marina District", "avail_start": 14*60+45, "avail_end": 19*60+30, "min_duration": 105},
    {"name": "Melissa", "location": "The Castro", "avail_start": 9*60+30, "avail_end": 17*60, "min_duration": 30},
    {"name": "Jeffrey", "location": "Fisherman's Wharf", "avail_start": 12*60+45, "avail_end": 18*60+45, "min_duration": 120},
    {"name": "Matthew", "location": "Bayview", "avail_start": 10*60+15, "avail_end": 13*60+15, "min_duration": 30},
    {"name": "Nancy", "location": "Pacific Heights", "avail_start": 17*60, "avail_end": 21*60+30, "min_duration": 105},
    {"name": "Karen", "location": "Mission District", "avail_start": 17*60+30, "avail_end": 20*60+30, "min_duration": 105},
    {"name": "Robert", "location": "Alamo Square", "avail_start": 11*60+15, "avail_end": 17*60+30, "min_duration": 120},
    {"name": "Joseph", "location": "Golden Gate Park", "avail_start": 8*60+30, "avail_end": 21*60+15, "min_duration": 105}
]

# Define the travel times (in minutes) between locations
travel_times = {
    "Presidio": {
        "Marina District": 11,
        "The Castro": 21,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Alamo Square": 19,
        "Golden Gate Park": 12,
    },
    "Marina District": {
        "Presidio": 10,
        "The Castro": 22,
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Pacific Heights": 7,
        "Mission District": 20,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
    },
    "The Castro": {
        "Presidio": 20,
        "Marina District": 21,
        "Fisherman's Wharf": 24,
        "Bayview": 19,
        "Pacific Heights": 16,
        "Mission District": 7,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Marina District": 9,
        "The Castro": 27,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Mission District": 22,
        "Alamo Square": 21,
        "Golden Gate Park": 25,
    },
    "Bayview": {
        "Presidio": 32,
        "Marina District": 27,
        "The Castro": 19,
        "Fisherman's Wharf": 25,
        "Pacific Heights": 23,
        "Mission District": 13,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Marina District": 6,
        "The Castro": 16,
        "Fisherman's Wharf": 13,
        "Bayview": 22,
        "Mission District": 15,
        "Alamo Square": 10,
        "Golden Gate Park": 15,
    },
    "Mission District": {
        "Presidio": 25,
        "Marina District": 19,
        "The Castro": 7,
        "Fisherman's Wharf": 22,
        "Bayview": 14,
        "Pacific Heights": 16,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
    },
    "Alamo Square": {
        "Presidio": 17,
        "Marina District": 15,
        "The Castro": 8,
        "Fisherman's Wharf": 19,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Golden Gate Park": 9,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Marina District": 16,
        "The Castro": 13,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Mission District": 17,
        "Alamo Square": 9,
    },
}

# Starting location and arrival time
start_location = "Presidio"
arrival_time = 9 * 60  # 9:00 AM in minutes from midnight

# Create an Optimize object
opt = Optimize()

num_friends = len(friends)

# Create decision variables for each friend meeting:
# pos[i]: order position in the itinerary (0 means not scheduled, 1..num_friends means scheduled order)
# start[i]: meeting start time (in minutes from midnight)
# end[i]: meeting end time (in minutes from midnight)
pos = [Int(f"pos_{i}") for i in range(num_friends)]
start_vars = [Int(f"start_{i}") for i in range(num_friends)]
end_vars = [Int(f"end_{i}") for i in range(num_friends)]

for i, friend in enumerate(friends):
    # pos is between 0 and num_friends (0 if not scheduled)
    opt.add(pos[i] >= 0, pos[i] <= num_friends)
    # If not scheduled (pos==0), then start and end are set to 0.
    # If scheduled (pos != 0), then meeting must lie within available window and satisfy minimum duration.
    opt.add(
        If(pos[i] == 0,
           And(start_vars[i] == 0, end_vars[i] == 0),
           And(start_vars[i] >= friend["avail_start"],
               end_vars[i] <= friend["avail_end"],
               end_vars[i] - start_vars[i] >= friend["min_duration"])
          )
    )

# Ensure that if two meetings are both scheduled, they receive distinct positions
for i in range(num_friends):
    for j in range(i + 1, num_friends):
        opt.add(Or(pos[i] == 0, pos[j] == 0, pos[i] != pos[j]))

# For sequential meetings, add travel time constraints.
# For any two meetings i and j that are both scheduled and if meeting i comes before meeting j in order,
# then the travel time from friend[i]'s location to friend[j]'s location must be accounted for.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        # Only add constraint if both meetings are scheduled and pos[i] < pos[j]
        travel_time = travel_times[loc_i][loc_j]
        opt.add(Implies(And(pos[i] != 0, pos[j] != 0, pos[i] < pos[j]),
                        end_vars[i] + travel_time <= start_vars[j]))

# For the first meeting in the itinerary, account for travel time from the starting location.
for i in range(num_friends):
    travel_time_from_start = travel_times[start_location][friends[i]["location"]]
    opt.add(Implies(pos[i] == 1, arrival_time + travel_time_from_start <= start_vars[i]))

# Define the objective: maximize number of meetings scheduled
num_meetings = Sum([If(pos[i] != 0, 1, 0) for i in range(num_friends)])
h = opt.maximize(num_meetings)

# Check for solution and extract model
if opt.check() == sat:
    model = opt.model()
    # Gather scheduled meetings with their order positions, start and end times
    itinerary = []
    scheduled = []
    for i in range(num_friends):
        p_val = model.evaluate(pos[i]).as_long()
        if p_val != 0:
            s_val = model.evaluate(start_vars[i]).as_long()
            e_val = model.evaluate(end_vars[i]).as_long()
            scheduled.append((p_val, friends[i]["name"], friends[i]["location"], s_val, e_val))
    # Sort scheduled meetings by their order position (lower pos means earlier)
    scheduled.sort(key=lambda x: x[0])
    for order_val, person, location, s_val, e_val in scheduled:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": format_time(s_val),
            "end_time": format_time(e_val)
        })
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))