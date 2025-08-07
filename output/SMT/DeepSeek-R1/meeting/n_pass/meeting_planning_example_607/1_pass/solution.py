import json
from z3 import *

# Travel data: list of (from, to, minutes)
travel_data = [
    ("Sunset District", "Russian Hill", 24),
    ("Sunset District", "The Castro", 17),
    ("Sunset District", "Richmond District", 12),
    ("Sunset District", "Marina District", 21),
    ("Sunset District", "North Beach", 29),
    ("Sunset District", "Union Square", 30),
    ("Sunset District", "Golden Gate Park", 11),
    ("Russian Hill", "Sunset District", 23),
    ("Russian Hill", "The Castro", 21),
    ("Russian Hill", "Richmond District", 14),
    ("Russian Hill", "Marina District", 7),
    ("Russian Hill", "North Beach", 5),
    ("Russian Hill", "Union Square", 11),
    ("Russian Hill", "Golden Gate Park", 21),
    ("The Castro", "Sunset District", 17),
    ("The Castro", "Russian Hill", 18),
    ("The Castro", "Richmond District", 16),
    ("The Castro", "Marina District", 21),
    ("The Castro", "North Beach", 20),
    ("The Castro", "Union Square", 19),
    ("The Castro", "Golden Gate Park", 11),
    ("Richmond District", "Sunset District", 11),
    ("Richmond District", "Russian Hill", 13),
    ("Richmond District", "The Castro", 16),
    ("Richmond District", "Marina District", 9),
    ("Richmond District", "North Beach", 17),
    ("Richmond District", "Union Square", 21),
    ("Richmond District", "Golden Gate Park", 9),
    ("Marina District", "Sunset District", 19),
    ("Marina District", "Russian Hill", 8),
    ("Marina District", "The Castro", 22),
    ("Marina District", "Richmond District", 11),
    ("Marina District", "North Beach", 11),
    ("Marina District", "Union Square", 16),
    ("Marina District", "Golden Gate Park", 18),
    ("North Beach", "Sunset District", 27),
    ("North Beach", "Russian Hill", 4),
    ("North Beach", "The Castro", 22),
    ("North Beach", "Richmond District", 18),
    ("North Beach", "Marina District", 9),
    ("North Beach", "Union Square", 7),
    ("North Beach", "Golden Gate Park", 22),
    ("Union Square", "Sunset District", 26),
    ("Union Square", "Russian Hill", 13),
    ("Union Square", "The Castro", 19),
    ("Union Square", "Richmond District", 20),
    ("Union Square", "Marina District", 18),
    ("Union Square", "North Beach", 10),
    ("Union Square", "Golden Gate Park", 22),
    ("Golden Gate Park", "Sunset District", 10),
    ("Golden Gate Park", "Russian Hill", 19),
    ("Golden Gate Park", "The Castro", 13),
    ("Golden Gate Park", "Richmond District", 7),
    ("Golden Gate Park", "Marina District", 16),
    ("Golden Gate Park", "North Beach", 24),
    ("Golden Gate Park", "Union Square", 22)
]

# Build travel time dictionary
travel = {}
districts = set()
for src, dst, t in travel_data:
    districts.add(src)
    districts.add(dst)
for d in districts:
    travel[d] = {}
for src, dst, t in travel_data:
    travel[src][dst] = t

# Define meetings: virtual meeting (index0) and real friends (index1-7)
meetings = []
# Virtual meeting: Start at Sunset District at time 0 (9:00 AM)
meetings.append( ("Start", "Sunset District", 0, 0, 0) )
# Real meetings: (name, district, available_start (min from 9:00), available_end (min from 9:00), min_duration)
meetings.append( ("Karen", "Russian Hill", 705, 765, 60) )      # 20:45 to 21:45
meetings.append( ("Jessica", "The Castro", 405, 630, 60) )      # 15:45 to 19:30
meetings.append( ("Matthew", "Richmond District", 0, 375, 15) )  # 9:00 to 15:15 (adjusted from 7:30 AM)
meetings.append( ("Michelle", "Marina District", 90, 585, 75) )  # 10:30 to 18:45
meetings.append( ("Carol", "North Beach", 180, 480, 90) )        # 12:00 to 17:00
meetings.append( ("Stephanie", "Union Square", 105, 315, 30) )   # 10:45 to 14:15
meetings.append( ("Linda", "Golden Gate Park", 105, 780, 90) )   # 10:45 to 22:00

n = len(meetings)  # 8 meetings

# Create Z3 variables
meet = [Bool(f"meet_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end = [Int(f"end_{i}") for i in range(n)]

solver = Solver()
opt = Optimize()

# Virtual meeting (index0) is fixed: meet[0]=True, start[0]=0, end[0]=0
solver.add(meet[0] == True)
solver.add(start[0] == 0)
solver.add(end[0] == 0)

# Constraints for real meetings (index1 to 7)
for i in range(1, n):
    name, district, avail_start, avail_end, duration = meetings[i]
    # If meeting i is selected, then:
    #   start[i] >= avail_start
    #   end[i] = start[i] + duration
    #   end[i] <= avail_end
    solver.add(Implies(meet[i], start[i] >= avail_start))
    solver.add(Implies(meet[i], end[i] == start[i] + duration))
    solver.add(Implies(meet[i], end[i] <= avail_end))

# Disjunctive constraints for every pair of meetings (including virtual)
for i in range(n):
    for j in range(i+1, n):
        dist_i = meetings[i][1]
        dist_j = meetings[j][1]
        travel_ij = travel[dist_i][dist_j]
        travel_ji = travel[dist_j][dist_i]
        # If both meetings i and j are selected, then:
        #   start[i] >= end[j] + travel from j to i OR start[j] >= end[i] + travel from i to j
        solver.add(Or(
            Not(meet[i]),
            Not(meet[j]),
            Or(
                start[i] >= end[j] + travel_ji,
                start[j] >= end[i] + travel_ij
            )
        ))

# Objective: maximize the number of real meetings (sum for i=1 to 7)
objective = Sum([If(meet[i], 1, 0) for i in range(1, n)])
opt.add(solver.assertions())
opt.maximize(objective)

# Solve and extract the itinerary
schedule_entries = []
if opt.check() == sat:
    model = opt.model()
    # For each real meeting, check if it was selected and get its start and end times
    for i in range(1, n):
        if model.evaluate(meet[i]):
            start_val = model.evaluate(start[i])
            end_val = model.evaluate(end[i])
            # Convert Z3 values to integers
            start_min = start_val.as_long() if is_int_value(start_val) else int(str(start_val))
            end_min = end_val.as_long() if is_int_value(end_val) else int(str(end_val))
            # Convert minutes to time strings (from 9:00 AM base)
            total_min_start = 9 * 60 + start_min
            total_min_end = 9 * 60 + end_min
            hours_start = total_min_start // 60
            minutes_start = total_min_start % 60
            hours_end = total_min_end // 60
            minutes_end = total_min_end % 60
            start_str = f"{hours_start:02d}:{minutes_start:02d}"
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            schedule_entries.append({
                "action": "meet",
                "person": meetings[i][0],
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort the itinerary by start time
    schedule_entries.sort(key=lambda x: x['start_time'])
    result = {"itinerary": schedule_entries}
else:
    result = {"itinerary": []}

print("SOLUTION:")
print(json.dumps(result))