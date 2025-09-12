from z3 import *
import json

def main():
    # Define location indices
    locations = {
        "Russian Hill": 0,
        "Presidio": 1,
        "Chinatown": 2,
        "Pacific Heights": 3,
        "Richmond District": 4,
        "Fisherman's Wharf": 5,
        "Golden Gate Park": 6,
        "Bayview": 7
    }
    
    location_names = ["Russian Hill", "Presidio", "Chinatown", "Pacific Heights", 
                     "Richmond District", "Fisherman's Wharf", "Golden Gate Park", "Bayview"]
    
    # Travel time matrix (8x8)
    travel = [
        [0, 14, 9, 7, 14, 7, 21, 23],
        [14, 0, 21, 11, 7, 19, 12, 31],
        [7, 19, 10, 10, 20, 8, 23, 22],
        [7, 11, 11, 0, 12, 13, 15, 22],
        [13, 7, 20, 10, 0, 18, 9, 26],
        [7, 17, 12, 12, 18, 0, 25, 26],
        [19, 11, 23, 16, 7, 24, 0, 23],
        [23, 31, 18, 23, 25, 25, 22, 0]
    ]
    
    # Meeting constraints (minutes from 9:00 AM)
    meetings = [
        {"name": "Matthew", "loc": 1, "start_avail": 120, "end_avail": 720, "min_dur": 90},
        {"name": "Margaret", "loc": 2, "start_avail": 15, "end_avail": 585, "min_dur": 90},
        {"name": "Nancy", "loc": 3, "start_avail": 315, "end_avail": 480, "min_dur": 15},
        {"name": "Helen", "loc": 4, "start_avail": 645, "end_avail": 780, "min_dur": 60},
        {"name": "Rebecca", "loc": 5, "start_avail": 735, "end_avail": 795, "min_dur": 60},
        {"name": "Kimberly", "loc": 6, "start_avail": 240, "end_avail": 450, "min_dur": 120},
        {"name": "Kenneth", "loc": 7, "start_avail": 330, "end_avail": 540, "min_dur": 60}
    ]
    
    # Initialize Z3 solver and variables
    s = Optimize()
    
    # Create variables for real meetings (index 1 to 7)
    held = [Bool(f"held_{i}") for i in range(1, 8)]
    start = [Int(f"start_{i}") for i in range(1, 8)]
    end = [Int(f"end_{i}") for i in range(1, 8)]
    
    # Virtual meeting (index 0)
    held0 = True
    start0 = 0
    end0 = 0
    loc0 = 0
    
    # Combine all meetings (including virtual)
    all_held = [held0] + held
    all_start = [start0] + start
    all_end = [end0] + end
    all_locations = [loc0] + [m["loc"] for m in meetings]
    
    # Add constraints for each real meeting
    for i in range(1, 8):
        m_info = meetings[i-1]
        s.add(Implies(held[i-1], start[i] >= m_info["start_avail"]))
        s.add(Implies(held[i-1], end[i] <= m_info["end_avail"]))
        s.add(Implies(held[i-1], end[i] - start[i] >= m_info["min_dur"]))
        s.add(Implies(held[i-1], start[i] >= 0))
        s.add(Implies(held[i-1], end[i] >= 0))
    
    # Add pairwise constraints for all meetings
    for i in range(8):
        for j in range(i+1, 8):
            constraint = Implies(
                And(all_held[i], all_held[j]),
                Or(
                    all_end[i] + travel[all_locations[i]][all_locations[j]] <= all_start[j],
                    all_end[j] + travel[all_locations[j]][all_locations[i]] <= all_start[i]
                )
            )
            s.add(constraint)
    
    # Maximize number of meetings
    s.maximize(Sum([If(h, 1, 0) for h in held]))
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes  # 9:00 AM in minutes from midnight
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 8):
            if is_true(model[held[i-1]]):
                s_val = model.evaluate(start[i]).as_long()
                e_val = model.evaluate(end[i]).as_long()
                start_str = minutes_to_time(s_val)
                end_str = minutes_to_time(e_val)
                itinerary.append({
                    "action": "meet",
                    "location": location_names[all_locations[i]],
                    "person": meetings[i-1]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        itinerary.sort(key=lambda x: x["start_time"])
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()