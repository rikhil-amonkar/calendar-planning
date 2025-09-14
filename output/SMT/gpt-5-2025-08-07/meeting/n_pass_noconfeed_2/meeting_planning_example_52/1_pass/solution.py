import json
from z3 import Optimize, Int, And

def time_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Input parameters (can be adjusted as needed)
    arrive_location = "Russian Hill"
    arrive_time = 9 * 60  # 9:00 => 540 minutes

    # Travel times (minutes)
    travel_RH_to_RD = 14
    travel_RD_to_RH = 13  # defined for completeness; not needed for this optimization

    # Barbara's availability at Richmond District (in minutes from midnight)
    barbara_location = "Richmond District"
    barbara_name = "Barbara"
    barbara_start = 13 * 60 + 15  # 13:15 => 795
    barbara_end = 18 * 60 + 15    # 18:15 => 1095
    barbara_min_meet = 45         # minutes

    # Z3 variables
    depart_RH_to_RD = Int("depart_RH_to_RD")
    arrive_RD = Int("arrive_RD")
    meet_start = Int("meet_start")
    meet_end = Int("meet_end")
    duration = Int("duration")

    opt = Optimize()

    # Core constraints
    opt.add(depart_RH_to_RD >= arrive_time)                          # Can't depart before arrival at Russian Hill
    opt.add(arrive_RD == depart_RH_to_RD + travel_RH_to_RD)          # Travel time to Richmond District
    opt.add(meet_start >= arrive_RD)                                 # Can't start meeting before arriving
    opt.add(meet_start >= barbara_start)                             # Can't start before Barbara is available
    opt.add(meet_end <= barbara_end)                                 # Must finish before Barbara leaves
    opt.add(duration == meet_end - meet_start)                       # Duration definition
    opt.add(duration >= barbara_min_meet)                            # Meet at least minimum duration
    opt.add(meet_end > meet_start)                                   # Positive meeting duration
    opt.add(meet_start >= 0, meet_end <= 24*60)                      # Bounds within the day

    # Optimization goals: maximize total meeting time, then start as early as possible
    opt.maximize(duration)
    opt.minimize(meet_start)

    result = opt.check()
    itinerary = []

    if str(result) == "sat":
        model = opt.model()
        ms = int(model[meet_start].as_long())
        me = int(model[meet_end].as_long())

        itinerary.append({
            "action": "meet",
            "location": barbara_location,
            "person": barbara_name,
            "start_time": time_to_str(ms),
            "end_time": time_to_str(me)
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()