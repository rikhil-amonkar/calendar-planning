import json
from functools import lru_cache

def time_to_min(t):
    # t like '9:00' or '18:45'
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mn = m % 60
    return f"{h}:{mn:02d}"

# Travel times in minutes (directed)
dist = {
    "Russian Hill": {
        "Marina District": 7,
        "Financial District": 11,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "The Castro": 21,
        "Bayview": 23,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Nob Hill": 5
    },
    "Marina District": {
        "Russian Hill": 8,
        "Financial District": 17,
        "Alamo Square": 15,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Sunset District": 19,
        "Haight-Ashbury": 16,
        "Nob Hill": 12
    },
    "Financial District": {
        "Russian Hill": 11,
        "Marina District": 15,
        "Alamo Square": 17,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Nob Hill": 8
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Marina District": 15,
        "Financial District": 17,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Sunset District": 16,
        "Haight-Ashbury": 5,
        "Nob Hill": 11
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Marina District": 16,
        "Financial District": 26,
        "Alamo Square": 9,
        "The Castro": 13,
        "Bayview": 23,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Nob Hill": 20
    },
    "The Castro": {
        "Russian Hill": 18,
        "Marina District": 21,
        "Financial District": 21,
        "Alamo Square": 8,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Nob Hill": 16
    },
    "Bayview": {
        "Russian Hill": 23,
        "Marina District": 27,
        "Financial District": 19,
        "Alamo Square": 16,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Sunset District": 23,
        "Haight-Ashbury": 19,
        "Nob Hill": 20
    },
    "Sunset District": {
        "Russian Hill": 24,
        "Marina District": 21,
        "Financial District": 30,
        "Alamo Square": 17,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Nob Hill": 27
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Marina District": 17,
        "Financial District": 21,
        "Alamo Square": 5,
        "Golden Gate Park": 7,
        "The Castro": 6,
        "Bayview": 18,
        "Sunset District": 15,
        "Nob Hill": 15
    },
    "Nob Hill": {
        "Russian Hill": 5,
        "Marina District": 11,
        "Financial District": 9,
        "Alamo Square": 11,
        "Golden Gate Park": 17,
        "The Castro": 17,
        "Bayview": 19,
        "Sunset District": 24,
        "Haight-Ashbury": 13
    }
}

# Participants constraints
participants = [
    # name, location, start, end, min_duration
    ("Mark", "Marina District", time_to_min("18:45"), time_to_min("21:00"), 90),
    ("Karen", "Financial District", time_to_min("9:30"), time_to_min("12:45"), 90),
    ("Barbara", "Alamo Square", time_to_min("10:00"), time_to_min("19:30"), 90),
    ("Nancy", "Golden Gate Park", time_to_min("16:45"), time_to_min("20:00"), 105),
    ("David", "The Castro", time_to_min("9:00"), time_to_min("18:00"), 120),
    ("Linda", "Bayview", time_to_min("18:15"), time_to_min("19:45"), 45),
    ("Kevin", "Sunset District", time_to_min("10:00"), time_to_min("17:45"), 120),
    ("Matthew", "Haight-Ashbury", time_to_min("10:15"), time_to_min("15:30"), 45),
    ("Andrew", "Nob Hill", time_to_min("11:45"), time_to_min("16:45"), 105),
]

name_to_index = {p[0]: i for i, p in enumerate(participants)}

start_location = "Russian Hill"
start_time = time_to_min("9:00")

N = len(participants)

# For reproducible and "smart" branching, sort participants by latest start (end - duration), then by window start
def latest_start(p):
    return p[3] - p[4]

order = sorted(range(N), key=lambda i: (latest_start(participants[i]), participants[i][2]))

# travel time helper
def travel_time(a, b):
    if a == b:
        return 0
    return dist[a][b]

# Objective comparator
def better(sol_a, sol_b):
    """
    Compare two solutions (schedules).
    Each solution is a dict:
      {
        'meetings': [ (name, location, start_min, end_min) ... ],
        'count': int,
        'total_meeting': int,
        'total_travel': int,
        'end_time': int
      }
    Returns True if sol_a is better than sol_b.
    """
    if sol_b is None:
        return True
    # primary: maximize count
    if sol_a['count'] != sol_b['count']:
        return sol_a['count'] > sol_b['count']
    # secondary: maximize total meeting minutes
    if sol_a['total_meeting'] != sol_b['total_meeting']:
        return sol_a['total_meeting'] > sol_b['total_meeting']
    # tertiary: minimize total travel
    if sol_a['total_travel'] != sol_b['total_travel']:
        return sol_a['total_travel'] < sol_b['total_travel']
    # quaternary: earliest end time
    if sol_a['end_time'] != sol_b['end_time']:
        return sol_a['end_time'] < sol_b['end_time']
    # finally: lexicographically smallest timeline (deterministic)
    a_times = [(m[2], m[3], m[0]) for m in sol_a['meetings']]
    b_times = [(m[2], m[3], m[0]) for m in sol_b['meetings']]
    return a_times < b_times

@lru_cache(maxsize=None)
def search(current_loc, current_time, visited_mask):
    best = None
    # Try scheduling each not-yet-met participant
    for idx in order:
        if (visited_mask >> idx) & 1:
            continue
        name, loc, start, end, dur = participants[idx]
        # compute earliest arrival
        t_travel = travel_time(current_loc, loc)
        arrival = current_time + t_travel
        # earliest feasible start
        earliest_start = max(arrival, start)
        latest_start_allowed = end - dur
        if earliest_start > latest_start_allowed:
            continue  # infeasible
        meet_start = earliest_start
        meet_end = meet_start + dur
        # recursively continue
        next_visited = visited_mask | (1 << idx)
        tail = search(loc, meet_end, next_visited)
        # Build current solution by prepending this meeting
        if tail is None:
            tail = {
                'meetings': [],
                'count': 0,
                'total_meeting': 0,
                'total_travel': 0,
                'end_time': current_time
            }
        cur = {
            'meetings': [(name, loc, meet_start, meet_end)] + tail['meetings'],
            'count': tail['count'] + 1,
            'total_meeting': tail['total_meeting'] + dur,
            'total_travel': tail['total_travel'] + t_travel,
            'end_time': tail['end_time'] if tail['meetings'] else meet_end
        }
        if best is None or better(cur, best):
            best = cur

    # Also allow stopping here (no more meetings)
    if best is None:
        # no further meetings feasible
        best = {
            'meetings': [],
            'count': 0,
            'total_meeting': 0,
            'total_travel': 0,
            'end_time': current_time
        }
    return best

# Run search
solution = search(start_location, start_time, 0)

# The recursive assembly added meetings in reverse chronological order due to prepending; sort by start time
itinerary_meetings = sorted(solution['meetings'], key=lambda m: m[2])

# Build JSON output
output = {"itinerary": []}
for name, loc, s, e in itinerary_meetings:
    output["itinerary"].append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": min_to_time(s),
        "end_time": min_to_time(e)
    })

print(json.dumps(output, ensure_ascii=False))