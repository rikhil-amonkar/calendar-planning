import json
from z3 import Optimize, Int, sat

def minutes_to_time_str(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def main():
    start_day = 9 * 60  # 540

    james_available_start = 765  # 12:45 PM (12*60+45)
    james_available_end = 840    # 2:00 PM (14*60)
    james_min_duration = 75

    robert_available_start = 765  # 12:45 PM
    robert_available_end = 915    # 3:15 PM (15*60+15)
    robert_min_duration = 30

    travel_NB_to_MD = 18  # North Beach to Mission District
    travel_MD_to_TC = 7   # Mission District to The Castro

    opt = Optimize()

    j_start = Int("j_start")
    j_end   = Int("j_end")
    r_start = Int("r_start")
    r_end   = Int("r_end")

    opt.add(j_start >= james_available_start)
    opt.add(j_end <= james_available_end)
    opt.add(j_end - j_start >= james_min_duration)
    opt.add(j_start >= start_day + travel_NB_to_MD)

    opt.add(r_start >= robert_available_start)
    opt.add(r_end <= robert_available_end)
    opt.add(r_end - r_start >= robert_min_duration)

    opt.add(r_start >= j_end + travel_MD_to_TC)

    total_meeting_duration = (j_end - j_start) + (r_end - r_start)
    opt.maximize(total_meeting_duration)

    result = opt.check()
    if result == sat:
        model = opt.model()
        j_start_val = model[j_start].as_long()
        j_end_val   = model[j_end].as_long()
        r_start_val = model[r_start].as_long()
        r_end_val   = model[r_end].as_long()

        itinerary = [
            {
                "action": "meet",
                "location": "Mission District",
                "person": "James",
                "start_time": minutes_to_time_str(j_start_val),
                "end_time": minutes_to_time_str(j_end_val)
            },
            {
                "action": "meet",
                "location": "The Castro",
                "person": "Robert",
                "start_time": minutes_to_time_str(r_start_val),
                "end_time": minutes_to_time_str(r_end_val)
            }
        ]
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"error": "No feasible schedule found"}))

if __name__ == "__main__":
    main()