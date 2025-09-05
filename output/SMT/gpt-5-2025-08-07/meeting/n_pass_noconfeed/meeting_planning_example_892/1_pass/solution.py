import json
from z3 import Int, Bool, Optimize, And, Or, Not, Implies, If

# Helper functions
def time_to_min(t):
    # t like "H:MM" in 24h not used here; we set directly by minutes
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Build travel times (minutes) between locations
travel = {
    "Marina District": {
        "Bayview": 27,
        "Sunset District": 19,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Chinatown": 15,
        "Haight-Ashbury": 16,
        "North Beach": 11,
        "Russian Hill": 8,
        "Embarcadero": 14,
    },
    "Bayview": {
        "Marina District": 27,
        "Sunset District": 23,
        "Richmond District": 25,
        "Nob Hill": 20,
        "Chinatown": 19,
        "Haight-Ashbury": 19,
        "North Beach": 22,
        "Russian Hill": 23,
        "Embarcadero": 19,
    },
    "Sunset District": {
        "Marina District": 21,
        "Bayview": 22,
        "Richmond District": 12,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Haight-Ashbury": 15,
        "North Beach": 28,
        "Russian Hill": 24,
        "Embarcadero": 30,
    },
    "Richmond District": {
        "Marina District": 9,
        "Bayview": 27,
        "Sunset District": 11,
        "Nob Hill": 17,
        "Chinatown": 20,
        "Haight-Ashbury": 10,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19,
    },
    "Nob Hill": {
        "Marina District": 11,
        "Bayview": 19,
        "Sunset District": 24,
        "Richmond District": 14,
        "Chinatown": 6,
        "Haight-Ashbury": 13,
        "North Beach": 8,
        "Russian Hill": 5,
        "Embarcadero": 9,
    },
    "Chinatown": {
        "Marina District": 12,
        "Bayview": 20,
        "Sunset District": 29,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Haight-Ashbury": 19,
        "North Beach": 3,
        "Russian Hill": 7,
        "Embarcadero": 5,
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Bayview": 18,
        "Sunset District": 15,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Chinatown": 19,
        "North Beach": 19,
        "Russian Hill": 17,
        "Embarcadero": 20,
    },
    "North Beach": {
        "Marina District": 9,
        "Bayview": 25,
        "Sunset District": 27,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Chinatown": 6,
        "Haight-Ashbury": 18,
        "Russian Hill": 4,
        "Embarcadero": 6,
    },
    "Russian Hill": {
        "Marina District": 7,
        "Bayview": 23,
        "Sunset District": 23,
        "Richmond District": 14,
        "Nob Hill": 5,
        "Chinatown": 9,
        "Haight-Ashbury": 17,
        "North Beach": 5,
        "Embarcadero": 8,
    },
    "Embarcadero": {
        "Marina District": 12,
        "Bayview": 21,
        "Sunset District": 30,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Chinatown": 7,
        "Haight-Ashbury": 21,
        "North Beach": 5,
        "Russian Hill": 8,
    }
}

# People with constraints
# Windows given in local time; convert to minutes from midnight
def hm_to_min(h, m):
    return h * 60 + m

people = [
    {
        "person": "Charles",
        "location": "Bayview",
        "start": hm_to_min(11, 30),
        "end": hm_to_min(14, 30),
        "min_duration": 45
    },
    {
        "person": "Robert",
        "location": "Sunset District",
        "start": hm_to_min(16, 45),
        "end": hm_to_min(21, 0),
        "min_duration": 30
    },
    {
        "person": "Karen",
        "location": "Richmond District",
        "start": hm_to_min(19, 15),
        "end": hm_to_min(21, 30),
        "min_duration": 60
    },
    {
        "person": "Rebecca",
        "location": "Nob Hill",
        "start": hm_to_min(16, 15),
        "end": hm_to_min(20, 30),
        "min_duration": 90
    },
    {
        "person": "Margaret",
        "location": "Chinatown",
        "start": hm_to_min(14, 15),
        "end": hm_to_min(19, 45),
        "min_duration": 120
    },
    {
        "person": "Patricia",
        "location": "Haight-Ashbury",
        "start": hm_to_min(14, 30),
        "end": hm_to_min(20, 30),
        "min_duration": 45
    },
    {
        "person": "Mark",
        "location": "North Beach",
        "start": hm_to_min(14, 0),
        "end": hm_to_min(18, 30),
        "min_duration": 105
    },
    {
        "person": "Melissa",
        "location": "Russian Hill",
        "start": hm_to_min(13, 0),
        "end": hm_to_min(19, 45),
        "min_duration": 30
    },
    {
        "person": "Laura",
        "location": "Embarcadero",
        "start": hm_to_min(7, 45),
        "end": hm_to_min(13, 15),
        "min_duration": 105
    },
]

# Origin node (index 0)
origin = {
    "person": "Origin",
    "location": "Marina District",
    "start": hm_to_min(9, 0),  # arrive at 9:00
    "end": hm_to_min(9, 0),
    "min_duration": 0
}

nodes = [origin] + people
N = len(nodes)

# Z3 variables
opt = Optimize()
opt.set(priority='lex')

attend = [Bool(f"attend_{i}") for i in range(N)]
start = [Int(f"start_{i}") for i in range(N)]
end = [Int(f"end_{i}") for i in range(N)]
dur = [Int(f"dur_{i}") for i in range(N)]
rank = [Int(f"rank_{i}") for i in range(N)]
earlier = [[Bool(f"earlier_{i}_{j}") if i != j else None for j in range(N)] for i in range(N)]

# Domain constraints
for i in range(N):
    opt.add(dur[i] >= 0)
    opt.add(start[i] >= 0)
    opt.add(end[i] >= 0)
    opt.add(rank[i] >= 0, rank[i] <= N-1)

# Origin fixed
opt.add(attend[0] == True)
opt.add(start[0] == origin["start"])
opt.add(dur[0] == 0)
opt.add(end[0] == origin["end"])
opt.add(rank[0] == 0)

# Constraints for real meetings
for i in range(1, N):
    node = nodes[i]
    # If attending, enforce window and duration minimum
    opt.add(Implies(attend[i], And(
        start[i] >= node["start"],
        end[i] <= node["end"],
        dur[i] >= node["min_duration"],
        end[i] == start[i] + dur[i],
        rank[i] >= 1  # strictly after origin in rank
    )))
    # If not attending, pin vars to 0 for cleanliness
    opt.add(Implies(Not(attend[i]), And(
        start[i] == 0, end[i] == 0, dur[i] == 0, rank[i] == 0
    )))

# Pairwise ordering and travel-time feasibility
for i in range(N):
    for j in range(i+1, N):
        li = nodes[i]["location"]
        lj = nodes[j]["location"]

        # Define when both are attended
        both_attended = And(attend[i], attend[j])

        # Total order among attended pairs
        opt.add(Implies(both_attended, Or(earlier[i][j], earlier[j][i])))
        opt.add(Implies(both_attended, Not(And(earlier[i][j], earlier[j][i]))))

        # If either not attended, no ordering
        opt.add(Implies(Not(both_attended), And(Not(earlier[i][j]), Not(earlier[j][i]))))

        # Travel-time and non-overlap when i before j
        if li in travel and lj in travel[li]:
            tij = travel[li][lj]
        else:
            # Should not happen with provided data; default large if missing
            tij = 10**6
        if lj in travel and li in travel[lj]:
            tji = travel[lj][li]
        else:
            tji = 10**6

        opt.add(Implies(And(both_attended, earlier[i][j]),
                        start[j] >= end[i] + tij))
        opt.add(Implies(And(both_attended, earlier[j][i]),
                        start[i] >= end[j] + tji))

        # Ranking consistency to prevent cycles
        opt.add(Implies(And(both_attended, earlier[i][j]), rank[i] + 1 <= rank[j]))
        opt.add(Implies(And(both_attended, earlier[j][i]), rank[j] + 1 <= rank[i]))

# Ensure origin is earlier than any attended real meeting, not vice versa
for i in range(1, N):
    li = nodes[0]["location"]  # Marina District
    lj = nodes[i]["location"]
    tij = travel[li][lj]
    # If attending i, origin must be earlier; i must not be earlier than origin
    opt.add(Implies(attend[i], earlier[0][i]))
    opt.add(Not(earlier[i][0]))
    # Travel constraint from origin to i when earlier[0][i]
    opt.add(Implies(earlier[0][i], start[i] >= end[0] + tij))
    # Rank consistency already covered by pairwise rules

# Objective: maximize number of attended meetings (excluding origin), then maximize total meeting time
total_attended = sum([If(attend[i], 1, 0) for i in range(1, N)])
total_duration = sum([dur[i] for i in range(1, N)])

opt.maximize(total_attended)
opt.maximize(total_duration)

# Solve
if opt.check() != None:
    model = opt.model()
    schedule = []
    for i in range(1, N):
        if model.evaluate(attend[i], model_completion=True):
            s = model.evaluate(start[i]).as_long()
            e = model.evaluate(end[i]).as_long()
            schedule.append({
                "person": nodes[i]["person"],
                "location": nodes[i]["location"],
                "start": s,
                "end": e
            })

    # Sort by start time
    schedule.sort(key=lambda x: x["start"])

    # Build JSON itinerary
    itinerary = []
    for item in schedule:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt(item["start"]),
            "end_time": fmt(item["end"])
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    # Infeasible (shouldn't happen with given data)
    print(json.dumps({"itinerary": []}, indent=2))