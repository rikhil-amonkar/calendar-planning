from z3 import *
import json

def main():
    meetings = [
        ("Laura", "Alamo Square", 870, 975, 75),      # 14:30 to 16:15 (75 min)
        ("Brian", "Presidio", 615, 1020, 30),         # 10:15 to 17:00 (30 min)
        ("Karen", "Russian Hill", 1080, 1215, 90),    # 18:00 to 20:15 (90 min)
        ("Stephanie", "North Beach", 615, 960, 75),   # 10:15 to 16:00 (75 min)
        ("Helen", "Golden Gate Park", 690, 1305, 120), # 11:30 to 21:45 (120 min)
        ("Sandra", "Richmond District", 480, 915, 30), # 8:00 to 15:15 (30 min) - earliest start 9:20
        ("Mary", "Embarcadero", 1005, 1125, 120),     # 16:45 to 18:45 (120 min)
        ("Deborah", "Financial District", 1140, 1245, 105), # 19:00 to 20:45 (105 min)
        ("Elizabeth", "Marina District", 510, 795, 105) # 8:30 to 13:15 (105 min) - earliest start 9:19
    ]
    
    travel_dict = {
        "Mission District": {
            "Alamo Square": 11,
            "Presidio": 25,
            "Russian Hill": 15,
            "North Beach": 17,
            "Golden Gate Park": 17,
            "Richmond District": 20,
            "Embarcadero": 19,
            "Financial District": 15,
            "Marina District": 19
        },
        "Alamo Square": {
            "Mission District": 10,
            "Presidio": 17,
            "Russian Hill": 13,
            "North Beach": 15,
            "Golden Gate Park": 9,
            "Richmond District": 11,
            "Embarcadero": 16,
            "Financial District": 17,
            "Marina District": 15
        },
        "Presidio": {
            "Mission District": 26,
            "Alamo Square": 19,
            "Russian Hill": 14,
            "North Beach": 18,
            "Golden Gate Park": 12,
            "Richmond District": 7,
            "Embarcadero": 20,
            "Financial District": 23,
            "Marina District": 11
        },
        "Russian Hill": {
            "Mission District": 16,
            "Alamo Square": 15,
            "Presidio": 14,
            "North Beach": 5,
            "Golden Gate Park": 21,
            "Richmond District": 14,
            "Embarcadero": 8,
            "Financial District": 11,
            "Marina District": 7
        },
        "North Beach": {
            "Mission District": 18,
            "Alamo Square": 16,
            "Presidio": 17,
            "Russian Hill": 4,
            "Golden Gate Park": 22,
            "Richmond District": 18,
            "Embarcadero": 6,
            "Financial District": 8,
            "Marina District": 9
        },
        "Golden Gate Park": {
            "Mission District": 17,
            "Alamo Square": 9,
            "Presidio": 11,
            "Russian Hill": 19,
            "North Beach": 23,
            "Richmond District": 7,
            "Embarcadero": 25,
            "Financial District": 26,
            "Marina District": 16
        },
        "Richmond District": {
            "Mission District": 20,
            "Alamo Square": 13,
            "Presidio": 7,
            "Russian Hill": 13,
            "North Beach": 17,
            "Golden Gate Park": 9,
            "Embarcadero": 19,
            "Financial District": 22,
            "Marina District": 9
        },
        "Embarcadero": {
            "Mission District": 20,
            "Alamo Square": 19,
            "Presidio": 20,
            "Russian Hill": 8,
            "North Beach": 5,
            "Golden Gate Park": 25,
            "Richmond District": 21,
            "Financial District": 5,
            "Marina District": 12
        },
        "Financial District": {
            "Mission District": 17,
            "Alamo Square": 17,
            "Presidio": 22,
            "Russian Hill": 11,
            "North Beach": 7,
            "Golden Gate Park": 23,
            "Richmond District": 21,
            "Embarcadero": 4,
            "Marina District": 15
        },
        "Marina District": {
            "Mission District": 20,
            "Alamo Square": 15,
            "Presidio": 10,
            "Russian Hill": 8,
            "North Beach": 11,
            "Golden Gate Park": 18,
            "Richmond District": 11,
            "Embarcadero": 14,
            "Financial District": 17
        }
    }
    
    s = Solver()
    opt = Optimize()
    
    meet_vars = []
    start_vars = []
    end_vars = []
    for i, (name, district, win_start, win_end, dur) in enumerate(meetings):
        meet_var = Bool(f'meet_{name}')
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meet_vars.append(meet_var)
        start_vars.append(start_var)
        end_vars.append(end_var)
        
        # If meeting, then constraints on time window and duration
        opt.add(Implies(meet_var, start_var >= win_start))
        opt.add(Implies(meet_var, end_var <= win_end))
        opt.add(Implies(meet_var, end_var == start_var + dur))
        
        # Constraint: start time must be at least the travel time from Mission District
        travel_time = travel_dict["Mission District"][district]
        opt.add(Implies(meet_var, start_var >= 540 + travel_time))
    
    # Pairwise constraints for every pair of meetings
    n = len(meetings)
    for i in range(n):
        for j in range(i+1, n):
            name_i, district_i, _, _, _ = meetings[i]
            name_j, district_j, _, _, _ = meetings[j]
            travel_ij = travel_dict[district_i][district_j]
            travel_ji = travel_dict[district_j][district_i]
            opt.add(Implies(And(meet_vars[i], meet_vars[j]),
                          Or(
                              start_vars[i] >= end_vars[j] + travel_ji,
                              start_vars[j] >= end_vars[i] + travel_ij
                          )))
    
    # Objective: maximize the number of meetings
    obj = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
    opt.maximize(obj)
    
    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if m.eval(meet_vars[i]):
                name = meetings[i][0]
                start_val = m.eval(start_vars[i]).as_long()
                end_val = m.eval(end_vars[i]).as_long()
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_time = f"{start_h:02d}:{start_m:02d}"
                end_time = f"{end_h:02d}:{end_m:02d}"
                scheduled_meetings.append((start_val, name, start_time, end_time))
        
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = []
        for (_, name, start_time, end_time) in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()