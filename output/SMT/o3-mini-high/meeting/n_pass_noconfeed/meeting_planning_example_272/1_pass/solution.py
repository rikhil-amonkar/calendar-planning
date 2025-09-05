import json
from z3 import Optimize, Int, Bool, If, And, Implies, sat

# Convert minutes since midnight to a formatted time string (24-hour, no leading zero for hours)
def minutes_to_time(minutes_value):
    hour = minutes_value // 60
    minute = minutes_value % 60
    return f"{hour}:{minute:02d}"

# Create an Optimize object
opt = Optimize()

# Time reference: times are in minutes from midnight.
# Your arrival at Russian Hill is at 9:00, i.e., 9*60 = 540.
start_base = 540

# Friend availability (in minutes from midnight)
# Patricia: 18:30 (18*60+30 = 1110) to 21:45 (21*60+45 = 1305)
pat_start_avail = 1110
pat_end_avail   = 1305
# Ashley: 20:30 (20*60+30 = 1230) to 21:15 (21*60+15 = 1275)
ash_start_avail = 1230
ash_end_avail   = 1275
# Timothy: 9:45 (9*60+45 = 585) to 17:45 (17*60+45 = 1065)
tim_start_avail = 585
tim_end_avail   = 1065

# Minimum meeting durations (in minutes)
min_dur_pat = 90
min_dur_ash = 45
min_dur_tim = 120

# Travel times (minutes) between locations:
# Locations: Russian Hill, Nob Hill, Mission District, Embarcadero
travel = {
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Embarcadero"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Embarcadero"): 9,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Embarcadero"): 19,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Mission District"): 20
}

# Define decision variables:
# For each friend meeting, we have a Boolean indicating if the meeting is scheduled,
# and Int variables for the meeting start and end times (in minutes from midnight).
x_tim = Bool("x_tim")  # Meeting with Timothy (at Embarcadero)
x_pat = Bool("x_pat")  # Meeting with Patricia (at Nob Hill)
x_ash = Bool("x_ash")  # Meeting with Ashley (at Mission District)

start_tim = Int("start_tim")
end_tim   = Int("end_tim")

start_pat = Int("start_pat")
end_pat   = Int("end_pat")

start_ash = Int("start_ash")
end_ash   = Int("end_ash")

# -------------------------------
# Add constraints for each meeting if scheduled
# -------------------------------

# Meeting with Timothy at Embarcadero:
# - You must travel from Russian Hill to Embarcadero: travel time = 8 minutes.
# - Timothy is available from tim_start_avail to tim_end_avail.
opt.add(Implies(x_tim, And(
    start_tim >= tim_start_avail,
    start_tim >= start_base + travel[("Russian Hill", "Embarcadero")],
    end_tim   <= tim_end_avail,
    end_tim - start_tim >= min_dur_tim
)))

# Meeting with Patricia at Nob Hill:
# - Patricia is available from pat_start_avail to pat_end_avail.
# - If meeting with Timothy occurred before, you travel from Embarcadero to Nob Hill (10 min);
#   otherwise, you come directly from Russian Hill to Nob Hill (5 min).
opt.add(Implies(x_pat, And(
    start_pat >= pat_start_avail,
    end_pat   <= pat_end_avail,
    end_pat - start_pat >= min_dur_pat,
    start_pat >= If(x_tim, end_tim + travel[("Embarcadero", "Nob Hill")],
                     start_base + travel[("Russian Hill", "Nob Hill")])
)))

# Meeting with Ashley at Mission District:
# - Ashley is available from ash_start_avail to ash_end_avail.
# - If Patricia meeting is scheduled, you travel from Nob Hill to Mission District (13 min);
#   else if Timothy meeting is scheduled, travel from Embarcadero to Mission District (20 min);
#   otherwise, travel from Russian Hill directly (16 min).
opt.add(Implies(x_ash, And(
    start_ash >= ash_start_avail,
    end_ash   <= ash_end_avail,
    end_ash - start_ash >= min_dur_ash,
    start_ash >= If(x_pat,
                    end_pat + travel[("Nob Hill", "Mission District")],
                    If(x_tim,
                       end_tim + travel[("Embarcadero", "Mission District")],
                       start_base + travel[("Russian Hill", "Mission District")]))
)))

# -------------------------------
# Objective: Maximize the number of meetings scheduled.
# -------------------------------
friend_count = If(x_tim, 1, 0) + If(x_pat, 1, 0) + If(x_ash, 1, 0)
opt.maximize(friend_count)

# -------------------------------
# Solve for an optimal schedule.
# -------------------------------
if opt.check() == sat:
    m = opt.model()
else:
    print(json.dumps({"itinerary": []}))
    exit(0)

# Prepare the itinerary list based on the model.
itinerary = []
meetings = []

# Extract meeting details from the model if scheduled.
if m.evaluate(x_tim):
    st = m.evaluate(start_tim).as_long()
    et = m.evaluate(end_tim).as_long()
    meetings.append(("Timothy", "Embarcadero", st, et))
if m.evaluate(x_pat):
    st = m.evaluate(start_pat).as_long()
    et = m.evaluate(end_pat).as_long()
    meetings.append(("Patricia", "Nob Hill", st, et))
if m.evaluate(x_ash):
    st = m.evaluate(start_ash).as_long()
    et = m.evaluate(end_ash).as_long()
    meetings.append(("Ashley", "Mission District", st, et))

# Sort the meetings in chronological order (by start time).
meetings.sort(key=lambda tup: tup[2])
for person, location, st, et in meetings:
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": minutes_to_time(st),
        "end_time": minutes_to_time(et)
    })

# Output the result as a JSON-formatted dictionary.
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))