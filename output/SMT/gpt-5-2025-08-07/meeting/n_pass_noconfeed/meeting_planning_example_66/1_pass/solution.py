import json
from z3 import Optimize, Int, And, If

def parse_time(tstr):
    # tstr like '9:00' or '13:30'
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def minutes_to_str(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

def plan_schedule():
    # Input parameters (can be adjusted as needed)
    origin = "Nob Hill"
    arrival_time_at_origin = "9:00"

    # Travel times in minutes
    travel_times = {
        ("Nob Hill", "Presidio"): 17,
        ("Presidio", "Nob Hill"): 18,
    }

    # Friend availability and constraints
    friend_name = "Robert"
    friend_location = "Presidio"
    friend_start = "11:15"
    friend_end = "17:45"
    min_meet_minutes = 120

    # Convert to minutes
    origin_arrival_min = parse_time(arrival_time_at_origin)
    friend_start_min = parse_time(friend_start)
    friend_end_min = parse_time(friend_end)
    travel_to_friend = travel_times[(origin, friend_location)]

    # Z3 variables
    D_NH = Int("depart_nob_hill_min")        # departure time from Nob Hill (minutes since midnight)
    S = Int("meeting_start_min")             # meeting start time
    E = Int("meeting_end_min")               # meeting end time

    opt = Optimize()

    # Bounds for the day (optional, but keeps times reasonable)
    day_start = 0
    day_end = 24 * 60 - 1

    opt.add(And(D_NH >= origin_arrival_min, D_NH <= day_end))
    opt.add(And(S >= day_start, S <= day_end))
    opt.add(And(E >= day_start, E <= day_end))

    # Must be at Presidio by meeting start time
    opt.add(S >= D_NH + travel_to_friend)

    # Friend availability window
    opt.add(S >= friend_start_min)
    opt.add(E <= friend_end_min)

    # Meeting duration constraints
    opt.add(E - S >= min_meet_minutes)

    # Optimize: maximize total meeting time with the friend
    duration = E - S
    opt.maximize(duration)

    # Optionally minimize waiting time at Presidio before meeting starts
    waiting_time = S - (D_NH + travel_to_friend)
    opt.minimize(If(waiting_time >= 0, waiting_time, 0))

    if opt.check() !=  sat:
        # Fallback if something goes wrong; return empty itinerary
        return {"itinerary": []}

    model = opt.model()
    s_val = model[S].as_long()
    e_val = model[E].as_long()

    itinerary = [
        {
            "action": "meet",
            "location": friend_location,
            "person": friend_name,
            "start_time": minutes_to_str(s_val),
            "end_time": minutes_to_str(e_val),
        }
    ]
    return {"itinerary": itinerary}

# Z3 returns 'sat' symbol; import after function to avoid top-level dependency during function def
from z3 import sat

if __name__ == "__main__":
    result = plan_schedule()
    print(json.dumps(result, ensure_ascii=False))