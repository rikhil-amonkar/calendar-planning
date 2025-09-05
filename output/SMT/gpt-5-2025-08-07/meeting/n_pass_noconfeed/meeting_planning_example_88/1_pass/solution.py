import json
from z3 import Int, Optimize, And, If, sat

def minutes_to_time_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Parameters (input variables)
    # Locations
    SUNSET = "Sunset District"
    GGP = "Golden Gate Park"

    # Arrival at Sunset at 9:00 (in minutes since midnight)
    arrive_sunset = 9 * 60  # 540

    # Travel times (in minutes)
    t_sunset_to_ggp = 11
    t_ggp_to_sunset = 10

    # Joshua's availability
    josh_name = "Joshua"
    josh_loc = GGP
    josh_start = 20 * 60 + 45  # 8:45 PM = 1245
    josh_end = 21 * 60 + 45    # 9:45 PM = 1305
    min_meet_minutes = 15

    # Day bounds (for sanity)
    day_start = 0
    day_end = 24 * 60 - 1  # 23:59 -> 1439

    # Decision variables
    depart_sunset_to_ggp = Int("depart_sunset_to_ggp")  # departure time from Sunset to GGP
    arrive_ggp = Int("arrive_ggp")                      # arrival time at GGP
    meet_start = Int("meet_start")                      # start meeting Joshua
    meet_end = Int("meet_end")                          # end meeting Joshua
    depart_ggp_to_sunset = Int("depart_ggp_to_sunset")  # optional: depart GGP back to Sunset
    arrive_sunset_back = Int("arrive_sunset_back")      # optional: arrive back at Sunset

    opt = Optimize()

    # Timing relations and bounds
    opt.add(depart_sunset_to_ggp >= arrive_sunset)
    opt.add(depart_sunset_to_ggp >= day_start, depart_sunset_to_ggp <= day_end)
    opt.add(arrive_ggp == depart_sunset_to_ggp + t_sunset_to_ggp)
    opt.add(arrive_ggp >= day_start, arrive_ggp <= day_end)

    # Meeting constraints with Joshua
    opt.add(meet_start >= arrive_ggp)                 # can't start before we arrive at GGP
    opt.add(meet_start >= josh_start)                 # can't start before Joshua is available
    opt.add(meet_end <= josh_end)                     # must end by the end of Joshua's slot
    opt.add(meet_end > meet_start)                    # positive duration
    opt.add((meet_end - meet_start) >= min_meet_minutes)
    opt.add(meet_start >= day_start, meet_start <= day_end)
    opt.add(meet_end >= day_start, meet_end <= day_end)

    # Optional return trip (account for travel time back if we leave immediately after meeting)
    opt.add(depart_ggp_to_sunset == meet_end)
    opt.add(arrive_sunset_back == depart_ggp_to_sunset + t_ggp_to_sunset)
    opt.add(arrive_sunset_back >= day_start, arrive_sunset_back <= 24 * 60 + 60)  # allow spillover past 24:00 minimally

    # Optimization goals:
    # 1) Maximize meeting duration with Joshua
    duration = meet_end - meet_start
    opt.maximize(duration)
    # 2) Leave Sunset as late as possible to minimize idle time at GGP
    opt.maximize(depart_sunset_to_ggp)

    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()

    ms = model[meet_start].as_long()
    me = model[meet_end].as_long()

    itinerary = [
        {
            "action": "meet",
            "location": josh_loc,
            "person": josh_name,
            "start_time": minutes_to_time_str(ms),
            "end_time": minutes_to_time_str(me)
        }
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()