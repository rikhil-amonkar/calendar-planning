import json
from z3 import Optimize, Int, Bool, And, Or, Not, Implies, If, is_true

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Input parameters
    locations = ["Embarcadero", "Financial District", "Alamo Square"]
    travel = {
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Alamo Square"): 17,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Financial District"): 17,
    }

    # Availability windows (minutes from midnight)
    # You arrive at Embarcadero at 9:00
    arrive_location = "Embarcadero"
    arrive_time = 9 * 60  # 540
    
    # Stephanie at Financial District 8:15 to 11:30, need >= 90 minutes
    s_loc = "Financial District"
    s_avail_start = 8 * 60 + 15   # 495
    s_avail_end = 11 * 60 + 30    # 690
    s_min_duration = 90

    # John at Alamo Square 10:15 to 20:45, need >= 30 minutes
    j_loc = "Alamo Square"
    j_avail_start = 10 * 60 + 15  # 615
    j_avail_end = 20 * 60 + 45    # 1245
    j_min_duration = 30

    # Z3 variables
    opt = Optimize()

    # Booleans indicating whether we meet each friend
    meet_s = Bool("meet_s")
    meet_j = Bool("meet_j")

    # Order variable when both are met
    s_first = Bool("s_first")  # True => Stephanie first, False => John first

    # Times in minutes since midnight
    s_start = Int("s_start")
    s_end = Int("s_end")
    s_dur = Int("s_dur")

    j_start = Int("j_start")
    j_end = Int("j_end")
    j_dur = Int("j_dur")

    # Basic non-negativity
    opt.add(s_start >= 0, s_end >= 0, s_dur >= 0)
    opt.add(j_start >= 0, j_end >= 0, j_dur >= 0)

    # Meeting window and duration constraints (conditional on choosing to meet)
    opt.add(Implies(meet_s,
                    And(s_start >= s_avail_start,
                        s_end <= s_avail_end,
                        s_dur == s_end - s_start,
                        s_dur >= s_min_duration)))
    opt.add(Implies(Not(meet_s),
                    And(s_start == 0, s_end == 0, s_dur == 0)))

    opt.add(Implies(meet_j,
                    And(j_start >= j_avail_start,
                        j_end <= j_avail_end,
                        j_dur == j_end - j_start,
                        j_dur >= j_min_duration)))
    opt.add(Implies(Not(meet_j),
                    And(j_start == 0, j_end == 0, j_dur == 0)))

    # Travel-time and ordering constraints
    # If only Stephanie is met
    opt.add(Implies(And(meet_s, Not(meet_j)),
                    s_start >= arrive_time + travel[(arrive_location, s_loc)]))

    # If only John is met
    opt.add(Implies(And(meet_j, Not(meet_s)),
                    j_start >= arrive_time + travel[(arrive_location, j_loc)]))

    # If both are met, enforce an order and travel between meetings
    opt.add(Implies(And(meet_s, meet_j, s_first),
                    And(
                        s_start >= arrive_time + travel[(arrive_location, s_loc)],
                        j_start >= s_end + travel[(s_loc, j_loc)]
                    )))
    opt.add(Implies(And(meet_s, meet_j, Not(s_first)),
                    And(
                        j_start >= arrive_time + travel[(arrive_location, j_loc)],
                        s_start >= j_end + travel[(j_loc, s_loc)]
                    )))

    # Objective: maximize number of meetings, then maximize total meeting time,
    # then minimize start times to reduce waiting (tie-breaker).
    count_meetings = If(meet_s, 1, 0) + If(meet_j, 1, 0)
    total_meeting_time = s_dur + j_dur

    opt.maximize(count_meetings)
    opt.maximize(total_meeting_time)
    # Tie-breaker to prefer earlier starts (when possible)
    opt.minimize(s_start + j_start)

    if opt.check() != None:
        model = opt.model()
        ms = is_true(model.evaluate(meet_s, model_completion=True))
        mj = is_true(model.evaluate(meet_j, model_completion=True))

        itinerary = []
        if ms:
            s_start_val = model.evaluate(s_start, model_completion=True).as_long()
            s_end_val = model.evaluate(s_end, model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": s_loc,
                "person": "Stephanie",
                "start_time": minutes_to_str(s_start_val),
                "end_time": minutes_to_str(s_end_val)
            })
        if mj:
            j_start_val = model.evaluate(j_start, model_completion=True).as_long()
            j_end_val = model.evaluate(j_end, model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": j_loc,
                "person": "John",
                "start_time": minutes_to_str(j_start_val),
                "end_time": minutes_to_str(j_end_val)
            })

        # Sort itinerary by start time
        def parse_time_str(t):
            h, m = t.split(":")
            return int(h) * 60 + int(m)

        itinerary.sort(key=lambda x: parse_time_str(x["start_time"]))

        output = {
            "itinerary": itinerary
        }
        print(json.dumps(output, ensure_ascii=False))
    else:
        print(json.dumps({"itinerary": []}, ensure_ascii=False))

if __name__ == "__main__":
    main()