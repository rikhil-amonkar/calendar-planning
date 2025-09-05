"SOLUTION:"

import json
import itertools

# Helper functions
def parse_time(t):
    # t format: 'H:MM' 24-hour
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(a, b, travel_matrix):
    return travel_matrix.get((a, b), None)

# Input variables (meeting constraints)
arrival_location = "Russian Hill"
arrival_time_str = "9:00"

friends = [
    {
        "name": "Barbara",
        "location": "Pacific Heights",
        "available_start": "7:15",
        "available_end": "22:00",
        "min_meet_duration": 60
    }
]

# Travel times (in minutes)
travel_times = {
    ("Russian Hill", "Pacific Heights"): 7,
    ("Pacific Heights", "Russian Hill"): 7
}

# Convert inputs to numeric minutes
arrival_time = parse_time(arrival_time_str)
for f in friends:
    f["avail_start_min"] = parse_time(f["available_start"])
    f["avail_end_min"] = parse_time(f["available_end"])

# Scheduling logic: maximize number of distinct friends met; tie-break by total meeting time, then earliest finish
best_schedule = []
best_score = (-1, -1, float('inf'))  # (friend_count, total_meeting_minutes, finish_time)

for order in itertools.permutations(friends):
    current_loc = arrival_location
    current_time = arrival_time
    schedule = []
    for f in order:
        t = get_travel_time(current_loc, f["location"], travel_times)
        if t is None:
            continue  # cannot travel; skip this friend
        arrival_at_friend = current_time + t
        start = max(arrival_at_friend, f["avail_start_min"])
        end_min = start + f["min_meet_duration"]
        if end_min <= f["avail_end_min"]:
            schedule.append({
                "person": f["name"],
                "location": f["location"],
                "start": start,
                "end": end_min,
                "avail_end": f["avail_end_min"]
            })
            current_time = end_min
            current_loc = f["location"]
        # else: cannot fit minimum meeting; skip

    if not schedule:
        score = (0, 0, float('inf'))
    else:
        total_minutes = sum(s["end"] - s["start"] for s in schedule)
        finish_time = schedule[-1]["end"]
        score = (len(schedule), total_minutes, finish_time)

    if (score[0] > best_score[0] or
        (score[0] == best_score[0] and score[1] > best_score[1]) or
        (score[0] == best_score[0] and score[1] == best_score[1] and score[2] < best_score[2])):
        best_schedule = schedule
        best_score = score

# Post-processing: extend meetings within availability without reducing count
# Extend from last to first, respecting travel time needed to next meeting
extended_schedule = [dict(s) for s in best_schedule]  # copy
for i in reversed(range(len(extended_schedule))):
    current = extended_schedule[i]
    # Max end is limited by availability
    max_end = current["avail_end"]
    if i < len(extended_schedule) - 1:
        nxt = extended_schedule[i + 1]
        # Need to leave enough time to travel to next meeting and arrive by its start
        travel_needed = get_travel_time(current["location"], nxt["location"], travel_times) or 0
        latest_departure = nxt["start"] - travel_needed
        max_end = min(max_end, latest_departure)
    if max_end > current["end"]:
        current["end"] = max_end

# Prepare JSON output
itinerary = []
for s in extended_schedule:
    itinerary.append({
        "action": "meet",
        "location": s["location"],
        "person": s["person"],
        "start_time": fmt_time(s["start"]),
        "end_time": fmt_time(s["end"])
    })

result = {"itinerary": itinerary}

print(json.dumps(result, ensure_ascii=False, indent=2))