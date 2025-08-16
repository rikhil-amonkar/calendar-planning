from z3 import *
import json

# Travel times (in minutes) between locations.
times = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
}

# Information for each friend.
# Times are in minutes from midnight.
# For example, 9:00 AM is 9*60 = 540.
persons = {
    "Sarah": {
        "location": "North Beach",
        "avail_start": 16 * 60,        # 16:00 -> 960
        "avail_end": 18 * 60 + 15,       # 18:15 -> 1095
        "min_duration": 60,
    },
    "Jeffrey": {
        "location": "Union Square",
        "avail_start": 15 * 60,        # 15:00 -> 900
        "avail_end": 22 * 60,          # 22:00 -> 1320
        "min_duration": 75,
    },
    "Brian": {
        "location": "Alamo Square",
        "avail_start": 16 * 60,         # 16:00 -> 960
        "avail_end": 17 * 60 + 30,        # 17:30 -> 1050
        "min_duration": 75,
    }
}

# Starting parameters
arrival = 9 * 60  # 9:00 AM => 540 minutes; initial location is Sunset District

# Create Z3 variables for the proposed meeting start times.
s_start = Int("s_start")  # Sarah meeting start time
j_start = Int("j_start")  # Jeffrey meeting start time
b_start = Int("b_start")  # Brian meeting start time

# Boolean variables indicating whether we schedule a meeting with the friend.
s_meet = Bool("s_meet")
j_meet = Bool("j_meet")
b_meet = Bool("b_meet")

# For simplicity, if a meeting is scheduled we assume we use exactly the minimum required duration.
s_duration = persons["Sarah"]["min_duration"]     # 60 minutes
j_duration = persons["Jeffrey"]["min_duration"]     # 75 minutes
b_duration = persons["Brian"]["min_duration"]       # 75 minutes

# Create the optimizer.
opt = Optimize()

# 1. Enforce the meeting windows.
opt.add(Implies(s_meet,
                And(s_start >= persons["Sarah"]["avail_start"],
                    s_start <= persons["Sarah"]["avail_end"] - s_duration)))
opt.add(Implies(j_meet,
                And(j_start >= persons["Jeffrey"]["avail_start"],
                    j_start <= persons["Jeffrey"]["avail_end"] - j_duration)))
opt.add(Implies(b_meet,
                And(b_start >= persons["Brian"]["avail_start"],
                    b_start <= persons["Brian"]["avail_end"] - b_duration)))

# 2. Enforce initial travel constraints.
# The first meeting must account for the travel time from Sunset District.
is_earliest_s = And(s_meet, Or(Not(j_meet), s_start <= j_start), Or(Not(b_meet), s_start <= b_start))
is_earliest_j = And(j_meet, Or(Not(s_meet), j_start <= s_start), Or(Not(b_meet), j_start <= b_start))
is_earliest_b = And(b_meet, Or(Not(s_meet), b_start <= s_start), Or(Not(j_meet), b_start <= j_start))

opt.add(Implies(is_earliest_s,
                s_start >= arrival + times[("Sunset District", persons["Sarah"]["location"])]))
opt.add(Implies(is_earliest_j,
                j_start >= arrival + times[("Sunset District", persons["Jeffrey"]["location"])]))
opt.add(Implies(is_earliest_b,
                b_start >= arrival + times[("Sunset District", persons["Brian"]["location"])]))

# 3. Enforce ordering/travel-time constraints between meetings.
# For any two meetings that are both scheduled, either one happens completely before the other
# (including travel time between the locations).
# Sarah and Jeffrey:
opt.add(Implies(And(s_meet, j_meet),
                Or(
                    # Sarah then Jeffrey:
                    s_start + s_duration + times[(persons["Sarah"]["location"], persons["Jeffrey"]["location"])] <= j_start,
                    # Jeffrey then Sarah:
                    j_start + j_duration + times[(persons["Jeffrey"]["location"], persons["Sarah"]["location"])] <= s_start
                )))

# Sarah and Brian:
opt.add(Implies(And(s_meet, b_meet),
                Or(
                    s_start + s_duration + times[(persons["Sarah"]["location"], persons["Brian"]["location"])] <= b_start,
                    b_start + b_duration + times[(persons["Brian"]["location"], persons["Sarah"]["location"])] <= s_start
                )))

# Jeffrey and Brian:
opt.add(Implies(And(j_meet, b_meet),
                Or(
                    j_start + j_duration + times[(persons["Jeffrey"]["location"], persons["Brian"]["location"])] <= b_start,
                    b_start + b_duration + times[(persons["Brian"]["location"], persons["Jeffrey"]["location"])] <= j_start
                )))

# 4. Set the optimization objective.
# Primary objective: maximize the number of meetings (i.e. the number of friends met).
# Secondary objective: maximize total meeting duration (to prefer meetings with longer sessions in a tie).
total_meetings = If(s_meet, 1, 0) + If(j_meet, 1, 0) + If(b_meet, 1, 0)
total_duration = If(s_meet, s_duration, 0) + If(j_meet, j_duration, 0) + If(b_meet, b_duration, 0)
opt.maximize(total_meetings)
opt.maximize(total_duration)

# 5. Solve the problem.
opt.check()
model = opt.model()

# Helper function: converts minutes (from midnight) to 24-hour HH:MM format.
def minutes_to_time(m):
    m = int(m)
    h = m // 60
    minute = m % 60
    return f"{h:02d}:{minute:02d}"

# Build the itinerary from the model.
itinerary = []
if is_true(model.evaluate(s_meet)):
    s_start_val = model.evaluate(s_start).as_long()
    s_end_val = s_start_val + s_duration
    itinerary.append({
        "action": "meet",
        "person": "Sarah",
        "start_time": minutes_to_time(s_start_val),
        "end_time": minutes_to_time(s_end_val)
    })
if is_true(model.evaluate(j_meet)):
    j_start_val = model.evaluate(j_start).as_long()
    j_end_val = j_start_val + j_duration
    itinerary.append({
        "action": "meet",
        "person": "Jeffrey",
        "start_time": minutes_to_time(j_start_val),
        "end_time": minutes_to_time(j_end_val)
    })
if is_true(model.evaluate(b_meet)):
    b_start_val = model.evaluate(b_start).as_long()
    b_end_val = b_start_val + b_duration
    itinerary.append({
        "action": "meet",
        "person": "Brian",
        "start_time": minutes_to_time(b_start_val),
        "end_time": minutes_to_time(b_end_val)
    })

# Sort the itinerary in chronological order based on start time.
itinerary.sort(key=lambda x: x["start_time"])

# Output the result as a JSON-formatted dictionary.
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))