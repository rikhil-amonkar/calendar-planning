from z3 import *
import json

# Helper function: convert minutes after 9:00 to HH:MM in 24-hour format.
def minutes_to_time(minutes):
    # 9:00 is the base
    total_minutes = 9 * 60 + minutes
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times in minutes between locations.
# The keys are origin locations, and the values are dictionaries mapping destination to travel time.
travel = {
    "Pacific Heights": {
        "Marina District": 6,
        "The Castro": 16,
        "Richmond District": 12,
        "Alamo Square": 10,
        "Financial District": 13,
        "Presidio": 11,
        "Mission District": 15,
        "Nob Hill": 8,
        "Russian Hill": 7
    },
    "Marina District": {
        "Pacific Heights": 7,
        "The Castro": 22,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Presidio": 10,
        "Mission District": 20,
        "Nob Hill": 12,
        "Russian Hill": 8
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Presidio": 20,
        "Mission District": 7,
        "Nob Hill": 16,
        "Russian Hill": 18
    },
    "Richmond District": {
        "Pacific Heights": 10,
        "Marina District": 9,
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Presidio": 7,
        "Mission District": 20,
        "Nob Hill": 17,
        "Russian Hill": 13
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Marina District": 15,
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Presidio": 17,
        "Mission District": 10,
        "Nob Hill": 11,
        "Russian Hill": 13
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Marina District": 15,
        "The Castro": 20,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Presidio": 22,
        "Mission District": 17,
        "Nob Hill": 8,
        "Russian Hill": 11
    },
    "Presidio": {
        "Pacific Heights": 11,
        "Marina District": 11,
        "The Castro": 21,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Mission District": 26,
        "Nob Hill": 18,
        "Russian Hill": 14
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Marina District": 19,
        "The Castro": 7,
        "Richmond District": 20,
        "Alamo Square": 11,
        "Financial District": 15,
        "Presidio": 25,
        "Nob Hill": 12,
        "Russian Hill": 15
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Marina District": 11,
        "The Castro": 17,
        "Richmond District": 14,
        "Alamo Square": 11,
        "Financial District": 9,
        "Presidio": 17,
        "Mission District": 13,
        "Russian Hill": 5
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Marina District": 7,
        "The Castro": 21,
        "Richmond District": 14,
        "Alamo Square": 15,
        "Financial District": 11,
        "Presidio": 14,
        "Mission District": 16,
        "Nob Hill": 5
    }
}

# Meeting definitions.
# Times are measured in minutes after 9:00 AM.
# For each meeting: person, location, available start, available end, and minimum meeting duration.
meetings_data = [
    {"person": "Linda",    "location": "Marina District",    "avail_start": 540, "avail_end": 780, "min_duration": 30}, # 18:00 to 22:00
    {"person": "Kenneth",  "location": "The Castro",         "avail_start": 345, "avail_end": 435, "min_duration": 30}, # 14:45 to 16:15
    {"person": "Kimberly", "location": "Richmond District",  "avail_start": 315, "avail_end": 780, "min_duration": 30}, # 14:15 to 22:00
    {"person": "Paul",     "location": "Alamo Square",       "avail_start": 720, "avail_end": 750, "min_duration": 15}, # 21:00 to 21:30
    {"person": "Carol",    "location": "Financial District", "avail_start": 75,  "avail_end": 180, "min_duration": 60}, # 10:15 to 12:00
    {"person": "Brian",    "location": "Presidio",           "avail_start": 60,  "avail_end": 750, "min_duration": 75}, # 10:00 to 21:30
    {"person": "Laura",    "location": "Mission District",   "avail_start": 435, "avail_end": 690, "min_duration": 30}, # 16:15 to 20:30
    {"person": "Sandra",   "location": "Nob Hill",           "avail_start": 15,  "avail_end": 570, "min_duration": 60}, # 9:15 to 18:30
    {"person": "Karen",    "location": "Russian Hill",       "avail_start": 570, "avail_end": 780, "min_duration": 75}  # 18:30 to 22:00
]

# Number of meetings
n = len(meetings_data)

# Create an Optimize solver.
opt = Optimize()

# For each meeting, create a Boolean variable indicating if it is scheduled
# and an integer variable for its start time (minutes after 9:00)
scheduled = []
start_vars = []
for i, m in enumerate(meetings_data):
    sch = Bool(f"scheduled_{i}")
    st = Int(f"start_{i}")
    scheduled.append(sch)
    start_vars.append(st)
    # If meeting is scheduled, then:
    # - it must start no earlier than its available start time,
    # - and finish (start + duration) no later than its available end time.
    # - also, you must account for travel from the initial location "Pacific Heights".
    opt.add(Implies(sch, st >= m["avail_start"]))
    opt.add(Implies(sch, st <= m["avail_end"] - m["min_duration"]))
    # Travel time from arrival location (Pacific Heights) to meeting location.
    travel_time_from_start = travel["Pacific Heights"][m["location"]]
    opt.add(Implies(sch, st >= travel_time_from_start))
    
# For any two meetings that are scheduled, ensure they do not overlap considering travel time.
# Since meeting duration is fixed to the minimum required (no benefit to extend),
# we assume finish time = start time + min_duration.
for i in range(n):
    for j in range(i+1, n):
        m_i = meetings_data[i]
        m_j = meetings_data[j]
        # Travel time needed if meeting i comes before j:
        travel_i_to_j = travel[m_i["location"]][m_j["location"]]
        # Travel time needed if meeting j comes before i:
        travel_j_to_i = travel[m_j["location"]][m_i["location"]]
        # If both meetings are scheduled, then either:
        # i finishes and then there's travel time to j before j starts,
        # or j finishes and then there's travel time to i before i starts.
        opt.add(Implies(And(scheduled[i], scheduled[j]),
                        Or(start_vars[i] >= start_vars[j] + m_j["min_duration"] + travel_j_to_i,
                           start_vars[j] >= start_vars[i] + m_i["min_duration"] + travel_i_to_j)))

# Objective: maximize the sum of scheduled meetings (i.e., meet as many friends as possible)
obj = Sum([If(s, 1, 0) for s in scheduled])
opt.maximize(obj)

# Check and get model
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    # Gather scheduled meetings with their computed start times.
    scheduled_meetings = []
    for i, m in enumerate(meetings_data):
        if is_true(model.evaluate(scheduled[i])):
            st = model.evaluate(start_vars[i]).as_long()
            finish = st + m["min_duration"]
            scheduled_meetings.append({
                "person": m["person"],
                "location": m["location"],
                "start": st,
                "finish": finish,
                "duration": m["min_duration"]
            })
    # Sort the scheduled meetings by start time.
    scheduled_meetings.sort(key=lambda x: x["start"])
    # Build the itinerary with proper time formatting.
    for meet in scheduled_meetings:
        itinerary.append({
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": minutes_to_time(meet["start"]),
            "end_time": minutes_to_time(meet["finish"])
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))