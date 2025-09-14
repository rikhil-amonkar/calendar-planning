import json
from z3 import Optimize, Int, Bool, If, And, Or, Not, is_true, sat

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Define Implies for brevity
def Implies(a, b):
    return Or(Not(a), b)

def main():
    # Input parameters (can be adjusted as needed)
    locations = ["Embarcadero", "Financial District", "Alamo Square"]

    travel = {
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Alamo Square"): 17,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Financial District"): 17,
    }

    arrival_location = "Embarcadero"
    arrival_time = minutes(9, 0)

    people = {
        "Stephanie": {
            "location": "Financial District",
            "start": minutes(8, 15),
            "end": minutes(11, 30),
            "min_duration": 90
        },
        "John": {
            "location": "Alamo Square",
            "start": minutes(10, 15),
            "end": minutes(20, 45),
            "min_duration": 30
        }
    }

    # Z3 variables
    s_start = Int("s_start")
    s_end   = Int("s_end")
    j_start = Int("j_start")
    j_end   = Int("j_end")

    meetS = Bool("meetS")
    meetJ = Bool("meetJ")
    orderSfirst = Bool("orderSfirst")  # relevant only if meeting both

    opt = Optimize()
    opt.set(priority="lex")

    # Time domain bounds
    for v in [s_start, s_end, j_start, j_end]:
        opt.add(v >= 0, v <= 24*60)

    # Availability and duration constraints
    s_loc = people["Stephanie"]["location"]
    j_loc = people["John"]["location"]

    s_avail_start = people["Stephanie"]["start"]
    s_avail_end   = people["Stephanie"]["end"]
    s_min_dur     = people["Stephanie"]["min_duration"]

    j_avail_start = people["John"]["start"]
    j_avail_end   = people["John"]["end"]
    j_min_dur     = people["John"]["min_duration"]

    # If meeting someone, their meeting must be within their window and meet min duration
    opt.add(Implies(meetS, And(
        s_start >= s_avail_start,
        s_end   <= s_avail_end,
        s_end - s_start >= s_min_dur,
        s_end > s_start
    )))
    opt.add(Implies(Not(meetS), s_start == s_end))

    opt.add(Implies(meetJ, And(
        j_start >= j_avail_start,
        j_end   <= j_avail_end,
        j_end - j_start >= j_min_dur,
        j_end > j_start
    )))
    opt.add(Implies(Not(meetJ), j_start == j_end))

    # Travel feasibility constraints
    t_arr_to_S = travel[(arrival_location, s_loc)]
    t_arr_to_J = travel[(arrival_location, j_loc)]
    t_S_to_J   = travel[(s_loc, j_loc)]
    t_J_to_S   = travel[(j_loc, s_loc)]

    # If meeting only Stephanie
    opt.add(Implies(And(meetS, Not(meetJ)),
                    s_start >= arrival_time + t_arr_to_S))
    # If meeting only John
    opt.add(Implies(And(meetJ, Not(meetS)),
                    j_start >= arrival_time + t_arr_to_J))

    # If meeting both, enforce order and travel times
    opt.add(Implies(And(meetS, meetJ, orderSfirst), And(
        s_start >= arrival_time + t_arr_to_S,
        j_start >= s_end + t_S_to_J
    )))
    opt.add(Implies(And(meetS, meetJ, Not(orderSfirst)), And(
        j_start >= arrival_time + t_arr_to_J,
        s_start >= j_end + t_J_to_S
    )))

    # Encourage at least one meeting
    opt.add(Or(meetS, meetJ))

    # Objective 1: maximize number of friends met
    count_met = If(meetS, 1, 0) + If(meetJ, 1, 0)
    opt.maximize(count_met)

    # Objective 2: minimize the end time of the last meeting (earliest finish)
    last_end = If(And(meetS, meetJ, orderSfirst),
                  j_end,
                  If(And(meetS, meetJ, Not(orderSfirst)),
                     s_end,
                     If(meetS, s_end,
                        If(meetJ, j_end, arrival_time))))
    opt.minimize(last_end)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return
    model = opt.model()

    meet_s_val = is_true(model.evaluate(meetS, model_completion=True))
    meet_j_val = is_true(model.evaluate(meetJ, model_completion=True))

    itinerary = []
    if meet_s_val:
        s_st = model.evaluate(s_start, model_completion=True).as_long()
        s_en = model.evaluate(s_end, model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Stephanie",
            "start_time": minutes_to_str(s_st),
            "end_time": minutes_to_str(s_en)
        })
    if meet_j_val:
        j_st = model.evaluate(j_start, model_completion=True).as_long()
        j_en = model.evaluate(j_end, model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "location": "Alamo Square",
            "person": "John",
            "start_time": minutes_to_str(j_st),
            "end_time": minutes_to_str(j_en)
        })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()