import json
from z3 import *

def main():
    # Travel times between locations (in minutes)
    # Locations: 0=Golden Gate Park, 1=Fisherman's Wharf, 2=Mission District, 3=Financial District, 4=Bayview
    travel_times = {
        (0, 1): 24, (0, 2): 17, (0, 3): 26, (0, 4): 23,
        (1, 0): 25, (1, 2): 22, (1, 3): 11, (1, 4): 26,
        (2, 0): 17, (2, 1): 22, (2, 3): 17, (2, 4): 15,
        (3, 0): 23, (3, 1): 10, (3, 2): 17, (3, 4): 19,
        (4, 0): 22, (4, 1): 25, (4, 2): 13, (4, 3): 19
    }
    
    meetings_info = [
        {"name": "Joseph", "loc": 1, "duration": 90, "window_low": 480, "window_high": 1050},   # 8:00 AM to 5:30 PM
        {"name": "Kevin", "loc": 2, "duration": 30, "window_low": 675, "window_high": 915},      # 11:15 AM to 3:15 PM
        {"name": "Barbara", "loc": 3, "duration": 15, "window_low": 630, "window_high": 990},    # 10:30 AM to 4:30 PM
        {"name": "Jeffrey", "loc": 4, "duration": 60, "window_low": 1050, "window_high": 1290}   # 5:30 PM to 9:30 PM
    ]
    
    # Create Z3 variables and info for each meeting
    meetings = []
    for info in meetings_info:
        name = info["name"]
        meetings.append({
            "name": name,
            "loc": info["loc"],
            "duration": info["duration"],
            "window_low": info["window_low"],
            "window_high": info["window_high"],
            "start": Int(f"s_{name}"),
            "order": Int(f"o_{name}"),
            "include": Bool(f"include_{name}")
        })
    
    opt = Optimize()
    n_meetings = len(meetings)
    
    # Total included meetings to maximize
    total_included = Sum([If(m['include'], 1, 0) for m in meetings])
    
    # Window constraints for included meetings
    for m in meetings:
        opt.add(Implies(m['include'], 
                 And(m['start'] >= m['window_low'], 
                     m['start'] + m['duration'] <= m['window_high'])))
    
    # Order constraints: if included, order index in [0, n-1] (n = total_included)
    n = total_included
    for m in meetings:
        opt.add(Implies(m['include'], And(m['order'] >= 0, m['order'] < n)))
    
    # Distinct order indices for included meetings
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            m1 = meetings[i]
            m2 = meetings[j]
            opt.add(Implies(And(m1['include'], m2['include']), m1['order'] != m2['order']))
    
    # First meeting constraint: if included and order=0, start after travel from GGP (location 0)
    for m in meetings:
        tt = travel_times.get((0, m['loc']), 1000)
        opt.add(Implies(And(m['include'], m['order'] == 0), m['start'] >= 540 + tt))
    
    # Consecutive meetings constraint
    for i in range(n_meetings):
        for j in range(n_meetings):
            if i == j:
                continue
            m_i = meetings[i]
            m_j = meetings[j]
            tt = travel_times.get((m_j['loc'], m_i['loc']), 1000)
            cond = And(m_i['include'], m_j['include'], m_j['order'] == m_i['order'] - 1)
            opt.add(Implies(cond, m_i['start'] >= m_j['start'] + m_j['duration'] + tt))
    
    # Maximize the number of included meetings
    opt.maximize(total_included)
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for m in meetings:
            if is_true(model.eval(m['include'])):
                order_val = model.eval(m['order']).as_long()
                start_val = model.eval(m['start']).as_long()
                end_val = start_val + m['duration']
                start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
                end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
                scheduled_meetings.append((order_val, {
                    "action": "meet",
                    "person": m['name'],
                    "start_time": start_time,
                    "end_time": end_time
                }))
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in scheduled_meetings]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()