import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, sat

def time_to_minutes(t):
    # t format: 'H:MM' or 'HH:MM'
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Input parameters (as variables, could be adjusted)
    locations = ["Fisherman's Wharf", "Nob Hill"]
    start_location = "Fisherman's Wharf"
    arrival_time_str = "9:00"

    # Travel times in minutes
    travel_times = {
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Nob Hill", "Fisherman's Wharf"): 11,
    }

    # Friends availability (single friend: Kenneth at Nob Hill)
    friend_name = "Kenneth"
    friend_location = "Nob Hill"
    friend_window_start_str = "14:15"
    friend_window_end_str = "19:45"
    min_meeting_duration = 90  # minutes

    # Convert to minutes
    arrival_time = time_to_minutes(arrival_time_str)
    friend_window_start = time_to_minutes(friend_window_start_str)
    friend_window_end = time_to_minutes(friend_window_end_str)

    # Z3 model
    opt = Optimize()

    # Decision variables
    meet_kenneth = Bool("meet_kenneth")
    meet_start = Int("meet_start")  # minutes since midnight
    meet_end = Int("meet_end")      # minutes since midnight
    meet_duration = Int("meet_duration")

    # Bounds for times during the day
    day_start = 0
    day_end = 24 * 60
    opt.add(meet_start >= day_start, meet_start <= day_end)
    opt.add(meet_end >= day_start, meet_end <= day_end)

    # Travel feasibility: starting at Fisherman's Wharf at 9:00, must be able to reach Nob Hill
    travel_fw_to_nh = travel_times[(start_location, friend_location)]
    earliest_possible_at_nh = arrival_time + travel_fw_to_nh

    # Meeting duration definition with conditional
    opt.add(meet_duration == If(meet_kenneth, meet_end - meet_start, 0))

    # If we meet, enforce constraints
    opt.add(Implies(meet_kenneth, And(
        meet_start >= earliest_possible_at_nh,
        meet_start >= friend_window_start,
        meet_end <= friend_window_end,
        meet_end > meet_start,
        meet_end - meet_start >= min_meeting_duration
    )))

    # If we don't meet, times can be arbitrary but keep duration 0
    opt.add(Implies(~meet_kenneth, meet_duration == 0))

    # Objectives:
    # 1) Maximize number of friends met (here just Kenneth)
    # 2) Maximize meeting duration
    # 3) Minimize start time to prefer earlier feasible meeting if multiple optimal durations
    obj1 = opt.maximize(If(meet_kenneth, 1, 0))
    obj2 = opt.maximize(meet_duration)
    obj3 = opt.minimize(meet_start)

    if opt.check() != sat:
        # No feasible plan (shouldn't happen with given data)
        result = {"itinerary": []}
        print(json.dumps(result, ensure_ascii=False))
        return

    model = opt.model()

    itinerary = []
    if model.evaluate(meet_kenneth, model_completion=True).is_true():
        s = model.evaluate(meet_start, model_completion=True).as_long()
        e = model.evaluate(meet_end, model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "location": friend_location,
            "person": friend_name,
            "start_time": minutes_to_time(s),
            "end_time": minutes_to_time(e),
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()