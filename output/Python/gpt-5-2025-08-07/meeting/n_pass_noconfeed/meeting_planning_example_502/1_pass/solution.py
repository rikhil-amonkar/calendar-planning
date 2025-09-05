import itertools
import json

# Helper functions for time conversion
def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables: travel times (directed, in minutes)
travel = {
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "North Beach"): 3,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "North Beach"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
}

# Participants and constraints
people = [
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "start": to_minutes("11:00"),
        "end": to_minutes("15:00"),
        "min_meet": 105,
    },
    {
        "name": "Karen",
        "location": "Chinatown",
        "start": to_minutes("13:45"),
        "end": to_minutes("16:30"),
        "min_meet": 15,
    },
    {
        "name": "Brian",
        "location": "Union Square",
        "start": to_minutes("15:00"),
        "end": to_minutes("17:15"),
        "min_meet": 30,
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "start": to_minutes("8:00"),
        "end": to_minutes("11:15"),
        "min_meet": 30,
    },
    {
        "name": "Joseph",
        "location": "Pacific Heights",
        "start": to_minutes("8:15"),
        "end": to_minutes("9:30"),
        "min_meet": 60,
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "start": to_minutes("14:30"),
        "end": to_minutes("20:45"),
        "min_meet": 120,
    },
]

# Start conditions
start_location = "Financial District"
start_time = to_minutes("9:00")

# Scheduling function for a given order
def schedule_for_order(order):
    current_time = start_time
    current_loc = start_location
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        # Travel to person's location
        tt = travel.get((current_loc, person["location"]))
        if tt is None:
            # If travel not defined, skip
            continue
        arrive_time = current_time + tt
        total_travel += tt

        # Compute meeting window
        meet_start = max(arrive_time, person["start"])
        wait = max(0, person["start"] - arrive_time)
        total_wait += wait

        meet_end = meet_start + person["min_meet"]

        # Check feasibility
        if meet_end <= person["end"]:
            itinerary.append({
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": fmt_time(meet_start),
                "end_time": fmt_time(meet_end),
            })
            current_time = meet_end
            current_loc = person["location"]
        else:
            # If not feasible, undo travel and wait accounting that would not actually occur
            total_travel -= tt
            total_wait -= wait
            # Skip meeting this person
            continue

    # Metrics
    count_met = len(itinerary)
    total_meeting_minutes = sum(
        to_minutes(item["end_time"]) - to_minutes(item["start_time"]) for item in itinerary
    )
    finish_time = current_time

    return {
        "itinerary": itinerary,
        "count_met": count_met,
        "total_meeting_minutes": total_meeting_minutes,
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
    }

# Explore schedules across permutations to find the best
best = None
best_key = None

for order in itertools.permutations(people):
    result = schedule_for_order(order)
    key = (
        result["count_met"],                     # maximize number met
        result["total_meeting_minutes"],         # then maximize total meeting minutes
        -result["finish_time"],                  # then prefer earlier finish
        -result["total_travel"],                 # then prefer less travel
        -result["total_wait"],                   # then prefer less waiting
    )
    if best is None or key > best_key:
        best = result
        best_key = key

# Output the best itinerary as requested JSON structure
output = {
    "itinerary": best["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))