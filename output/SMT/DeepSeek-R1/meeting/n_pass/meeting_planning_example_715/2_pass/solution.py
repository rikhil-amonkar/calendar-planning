from z3 import *
import json

def main():
    meetings = [
        {"name": "Amanda", "loc": "Marina District", "start_avail": 14*60+45, "end_avail": 19*60+30, "min_dur": 105},
        {"name": "Melissa", "loc": "The Castro", "start_avail": 9*60+30, "end_avail": 17*60, "min_dur": 30},
        {"name": "Jeffrey", "loc": "Fisherman's Wharf", "start_avail": 12*60+45, "end_avail": 18*60+45, "min_dur": 120},
        {"name": "Matthew", "loc": "Bayview", "start_avail": 10*60+15, "end_avail": 13*60+15, "min_dur": 30},
        {"name": "Nancy", "loc": "Pacific Heights", "start_avail": 17*60, "end_avail": 21*60+30, "min_dur": 105},
        {"name": "Karen", "loc": "Mission District", "start_avail": 17*60+30, "end_avail": 20*60+30, "min_dur": 105},
        {"name": "Robert", "loc": "Alamo Square", "start_avail": 11*60+15, "end_avail": 17*60+30, "min_dur": 120},
        {"name": "Joseph", "loc": "Golden Gate Park", "start_avail": 8*60+30, "end_avail": 21*60+15, "min_dur": 105}
    ]
    
    travel_time_dict = {
        ("Presidio", "Marina District"): 11,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Golden Gate Park"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Golden Gate Park"): 22,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Golden Gate Park"): 17,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9
    }

    n_meetings = len(meetings)
    s = [Int(f's_{i}') for i in range(n_meetings)]
    start_times = [Real(f'start_{i}') for i in range(n_meetings)]
    scheduled = [Bool(f'scheduled_{i}') for i in range(n_meetings)]

    solver = Solver()

    for i in range(n_meetings):
        solver.add(Or(And(s[i] >= 0, s[i] < n_meetings), s[i] == -1))

    for i in range(n_meetings - 1):
        solver.add(If(s[i] == -1, s[i+1] == -1, True))

    for i in range(n_meetings):
        solver.add(scheduled[i] == Or([s[j] == i for j in range(n_meetings)]))

    for j in range(n_meetings):
        for k in range(j+1, n_meetings):
            solver.add(If(And(s[j] != -1, s[k] != -1), s[j] != s[k], True))

    for i in range(n_meetings):
        if i == 0:
            for meet_idx in range(n_meetings):
                loc = meetings[meet_idx]['loc']
                solver.add(If(s[0] == meet_idx,
                             start_times[meet_idx] >= 540 + travel_time_dict[("Presidio", loc)],
                             True))
        else:
            for meet_idx_current in range(n_meetings):
                for meet_idx_prev in range(n_meetings):
                    loc_prev = meetings[meet_idx_prev]['loc']
                    loc_current = meetings[meet_idx_current]['loc']
                    if loc_prev == loc_current:
                        travel_val = 0
                    else:
                        travel_val = travel_time_dict[(loc_prev, loc_current)]
                    solver.add(If(And(s[i] == meet_idx_current, s[i-1] == meet_idx_prev),
                                start_times[meet_idx_current] >= start_times[meet_idx_prev] + meetings[meet_idx_prev]['min_dur'] + travel_val,
                                True))

    for i in range(n_meetings):
        m = meetings[i]
        solver.add(If(scheduled[i],
                     And(start_times[i] >= m['start_avail'],
                         start_times[i] + m['min_dur'] <= m['end_avail']),
                     True))

    total_scheduled = Sum([If(scheduled[i], 1, 0) for i in range(n_meetings)])
    opt = Optimize()
    opt.add(solver.assertions())
    opt.maximize(total_scheduled)

    if opt.check() == sat:
        model = opt.model()
        itinerary_list = []
        for slot in range(n_meetings):
            s_val = model.eval(s[slot])
            if s_val.as_long() == -1:
                continue
            meet_idx = s_val.as_long()
            start_val = model.eval(start_times[meet_idx])
            if is_rational_value(start_val):
                num = start_val.numerator_as_long()
                den = start_val.denominator_as_long()
                start_minutes = num / den
            else:
                start_minutes = float(str(start_val))
            start_minutes = round(start_minutes)
            end_minutes = start_minutes + meetings[meet_idx]['min_dur']
            start_hour = start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = end_minutes // 60
            end_minute = end_minutes % 60
            start_str = f"{int(start_hour):02d}:{int(start_minute):02d}"
            end_str = f"{int(end_hour):02d}:{int(end_minute):02d}"
            itinerary_list.append({
                "action": "meet",
                "person": meetings[meet_idx]['name'],
                "start_time": start_str,
                "end_time": end_str
            })
        result = {"itinerary": itinerary_list}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()