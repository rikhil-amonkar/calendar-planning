import json
from z3 import Optimize, Int, Bool, And, Or, Implies, If, Sum, is_true, sat

def minutes(h, m):
    return h * 60 + m

def parse_time_24(t):
    # t like "9:00" or "13:30"
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Union Square",
    "The Castro",
    "North Beach",
    "Embarcadero",
    "Alamo Square",
    "Nob Hill",
    "Presidio",
    "Fisherman's Wharf",
    "Mission District",
    "Haight-Ashbury",
]

# Travel times (minutes)
travel = {
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Embarcadero": 11,
        "Alamo Square": 15,
        "Nob Hill": 9,
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Mission District": 14,
        "Haight-Ashbury": 18,
    },
    "The Castro": {
        "Union Square": 19,
        "North Beach": 20,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Nob Hill": 16,
        "Presidio": 20,
        "Fisherman's Wharf": 24,
        "Mission District": 7,
        "Haight-Ashbury": 6,
    },
    "North Beach": {
        "Union Square": 7,
        "The Castro": 23,
        "Embarcadero": 6,
        "Alamo Square": 16,
        "Nob Hill": 7,
        "Presidio": 17,
        "Fisherman's Wharf": 5,
        "Mission District": 18,
        "Haight-Ashbury": 18,
    },
    "Embarcadero": {
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Alamo Square": 19,
        "Nob Hill": 10,
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Mission District": 20,
        "Haight-Ashbury": 21,
    },
    "Alamo Square": {
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Embarcadero": 16,
        "Nob Hill": 11,
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Mission District": 10,
        "Haight-Ashbury": 5,
    },
    "Nob Hill": {
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Embarcadero": 9,
        "Alamo Square": 11,
        "Presidio": 17,
        "Fisherman's Wharf": 10,
        "Mission District": 13,
        "Haight-Ashbury": 13,
    },
    "Presidio": {
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Embarcadero": 20,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Mission District": 26,
        "Haight-Ashbury": 15,
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Embarcadero": 8,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Mission District": 22,
        "Haight-Ashbury": 22,
    },
    "Mission District": {
        "Union Square": 15,
        "The Castro": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Alamo Square": 11,
        "Nob Hill": 12,
        "Presidio": 25,
        "Fisherman's Wharf": 22,
        "Haight-Ashbury": 12,
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "The Castro": 6,
        "North Beach": 19,
        "Embarcadero": 20,
        "Alamo Square": 5,
        "Nob Hill": 15,
        "Presidio": 15,
        "Fisherman's Wharf": 23,
        "Mission District": 11,
    },
}

# People constraints: person -> (location, window_start, window_end, min_duration)
people = {
    "Melissa": ("The Castro", parse_time_24("20:15"), parse_time_24("21:15"), 30),
    "Kimberly": ("North Beach", parse_time_24("7:00"), parse_time_24("10:30"), 15),
    "Joseph": ("Embarcadero", parse_time_24("15:30"), parse_time_24("19:30"), 75),
    "Barbara": ("Alamo Square", parse_time_24("20:45"), parse_time_24("21:45"), 15),
    "Kenneth": ("Nob Hill", parse_time_24("12:15"), parse_time_24("17:15"), 105),
    "Joshua": ("Presidio", parse_time_24("16:30"), parse_time_24("18:15"), 105),
    "Brian": ("Fisherman's Wharf", parse_time_24("9:30"), parse_time_24("15:30"), 45),
    "Steven": ("Mission District", parse_time_24("19:30"), parse_time_24("21:00"), 90),
    "Betty": ("Haight-Ashbury", parse_time_24("19:00"), parse_time_24("20:30"), 90),
}

start_location = "Union Square"
arrival_time = parse_time_24("9:00")

# Build model
opt = Optimize()
opt.set(priority='lex')

persons = list(people.keys())

meet = {p: Bool(f"meet_{p}") for p in persons}
start = {p: Int(f"start_{p}") for p in persons}
end = {p: Int(f"end_{p}") for p in persons}
dur = {p: Int(f"dur_{p}") for p in persons}

# Bounds and per-person constraints
for p in persons:
    loc, w_start, w_end, min_dur = people[p]
    opt.add(And(start[p] >= 0, start[p] <= 24 * 60))
    opt.add(And(end[p] >= 0, end[p] <= 24 * 60))
    opt.add(And(dur[p] >= 0, dur[p] <= (w_end - w_start)))
    # If meeting, respect window and duration
    opt.add(Implies(meet[p], And(
        start[p] >= w_start,
        end[p] <= w_end,
        dur[p] >= min_dur,
        end[p] == start[p] + dur[p]
    )))
    # If not meeting, times collapse to zero
    opt.add(Implies(~meet[p], And(
        dur[p] == 0,
        start[p] == 0,
        end[p] == 0
    )))
    # Must be reachable from starting location at 9:00
    opt.add(Implies(meet[p], start[p] >= arrival_time + travel[start_location][loc]))

# Pairwise sequencing with travel times
order = {}
for i in range(len(persons)):
    for j in range(i + 1, len(persons)):
        pi = persons[i]
        pj = persons[j]
        li, lj = people[pi][0], people[pj][0]
        order_ij = Bool(f"order_{pi}_{pj}")  # True means i before j, else j before i
        order[(pi, pj)] = order_ij
        opt.add(Implies(And(meet[pi], meet[pj]),
                        Or(
                            And(order_ij, start[pj] >= end[pi] + travel[li][lj]),
                            And(~order_ij, start[pi] >= end[pj] + travel[lj][li])
                        )))

# Objectives: maximize number of people met, then total meeting time
opt.maximize(Sum([If(meet[p], 1, 0) for p in persons]))
opt.maximize(Sum([dur[p] for p in persons]))

result = opt.check()
itinerary = []

if result == sat:
    m = opt.model()
    meetings = []
    for p in persons:
        if is_true(m.evaluate(meet[p], model_completion=True)):
            s = m.evaluate(start[p], model_completion=True).as_long()
            e = m.evaluate(end[p], model_completion=True).as_long()
            loc = people[p][0]
            meetings.append((s, e, loc, p))
    meetings.sort(key=lambda x: x[0])
    for s, e, loc, p in meetings:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": p,
            "start_time": fmt_time(s),
            "end_time": fmt_time(e)
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False, indent=2))