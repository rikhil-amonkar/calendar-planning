import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, is_true, sat

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Input parameters
    arrive_location = "North Beach"
    arrive_time = 9 * 60  # 9:00 -> 540

    # Travel times in minutes
    travel = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Mission District"): 7,
    }

    # Friends' availability and required meeting durations
    # Times in minutes from midnight
    friends = {
        "James": {
            "location": "Mission District",
            "avail_start": 12 * 60 + 45,  # 12:45 -> 765
            "avail_end": 14 * 60,         # 14:00 -> 840
            "min_duration": 75
        },
        "Robert": {
            "location": "The Castro",
            "avail_start": 12 * 60 + 45,  # 12:45 -> 765
            "avail_end": 15 * 60 + 15,    # 15:15 -> 915
            "min_duration": 30
        }
    }

    def T(a, b):
        return travel[(a, b)]

    # Z3 variables
    s_j, e_j = Int('s_j'), Int('e_j')  # James start, end
    s_r, e_r = Int('s_r'), Int('e_r')  # Robert start, end
    meet_j, meet_r = Bool('meet_j'), Bool('meet_r')
    j_before_r = Bool('j_before_r')  # order boolean when meeting both

    opt = Optimize()
    opt.set(priority='lex')

    # Domains for time variables
    max_day = 24 * 60
    for v in [s_j, e_j, s_r, e_r]:
        opt.add(v >= 0, v <= max_day)

    # Meeting constraints for James
    j_loc = friends["James"]["location"]
    j_av_s = friends["James"]["avail_start"]
    j_av_e = friends["James"]["avail_end"]
    j_min = friends["James"]["min_duration"]

    opt.add(Implies(meet_j, And(
        s_j >= j_av_s,
        e_j <= j_av_e,
        e_j - s_j >= j_min,
        s_j < e_j
    )))

    # Meeting constraints for Robert
    r_loc = friends["Robert"]["location"]
    r_av_s = friends["Robert"]["avail_start"]
    r_av_e = friends["Robert"]["avail_end"]
    r_min = friends["Robert"]["min_duration"]

    opt.add(Implies(meet_r, And(
        s_r >= r_av_s,
        e_r <= r_av_e,
        e_r - s_r >= r_min,
        s_r < e_r
    )))

    # Travel feasibility from arrival to the first meeting
    opt.add(Implies(And(meet_j, Not(meet_r)),
                    arrive_time + T(arrive_location, j_loc) <= s_j))
    opt.add(Implies(And(meet_r, Not(meet_j)),
                    arrive_time + T(arrive_location, r_loc) <= s_r))
    opt.add(Implies(And(meet_j, meet_r, j_before_r),
                    arrive_time + T(arrive_location, j_loc) <= s_j))
    opt.add(Implies(And(meet_j, meet_r, Not(j_before_r)),
                    arrive_time + T(arrive_location, r_loc) <= s_r))

    # Inter-meeting travel feasibility if meeting both
    opt.add(Implies(And(meet_j, meet_r, j_before_r),
                    e_j + T(j_loc, r_loc) <= s_r))
    opt.add(Implies(And(meet_j, meet_r, Not(j_before_r)),
                    e_r + T(r_loc, j_loc) <= s_j))

    # Objective 1: Maximize number of friends met
    num_met = If(meet_j, 1, 0) + If(meet_r, 1, 0)
    opt.maximize(num_met)

    # Objective 2: Maximize total meeting time
    total_meet_time = If(meet_j, e_j - s_j, 0) + If(meet_r, e_r - s_r, 0)
    opt.maximize(total_meet_time)

    # Objective 3: Minimize finishing time (earlier end is better in tie)
    last_end = If(And(meet_j, meet_r),
                  If(j_before_r, e_r, e_j),
                  If(meet_j, e_j, If(meet_r, e_r, arrive_time)))
    opt.minimize(last_end)

    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = opt.model()

    itinerary = []

    if is_true(m.evaluate(meet_j)):
        sj = m.evaluate(s_j).as_long()
        ej = m.evaluate(e_j).as_long()
        itinerary.append({
            "action": "meet",
            "location": j_loc,
            "person": "James",
            "start_time": minutes_to_str(sj),
            "end_time": minutes_to_str(ej)
        })

    if is_true(m.evaluate(meet_r)):
        sr = m.evaluate(s_r).as_long()
        er = m.evaluate(e_r).as_long()
        itinerary.append({
            "action": "meet",
            "location": r_loc,
            "person": "Robert",
            "start_time": minutes_to_str(sr),
            "end_time": minutes_to_str(er)
        })

    # Sort itinerary by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()