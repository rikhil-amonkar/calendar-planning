from z3 import *
import json

def main():
    # Build travel times dictionary
    travel_times = {
        "Nob Hill": {
            "Richmond District": 14,
            "Financial District": 9,
            "North Beach": 8,
            "The Castro": 17,
            "Golden Gate Park": 17
        },
        "Richmond District": {
            "Nob Hill": 17,
            "Financial District": 22,
            "North Beach": 17,
            "The Castro": 16,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "Nob Hill": 8,
            "Richmond District": 21,
            "North Beach": 7,
            "The Castro": 23,
            "Golden Gate Park": 23
        },
        "North Beach": {
            "Nob Hill": 7,
            "Richmond District": 18,
            "Financial District": 8,
            "The Castro": 22,
            "Golden Gate Park": 22
        },
        "The Castro": {
            "Nob Hill": 16,
            "Richmond District": 16,
            "Financial District": 20,
            "North Beach": 20,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Nob Hill": 20,
            "Richmond District": 7,
            "Financial District": 26,
            "North Beach": 24,
            "The Castro": 13
        }
    }
    
    # Define activities: (index, location, duration, window_start, window_end) in minutes from 9:00 AM
    activities = [
        (0, "Nob Hill", 0, 0, 0),   # start activity
        (1, "Golden Gate Park", 120, 135, 330), # Jeffrey: 11:15AM to 2:30PM -> 135 to 330 minutes from 9:00 AM
        (2, "The Castro", 90, 285, 735),       # Deborah: 1:45PM to 9:15PM -> 285 to 735 minutes
        (3, "Financial District", 75, 450, 675), # Margaret: 4:30PM to 8:15PM -> 450 to 675 minutes
        (4, "North Beach", 45, 570, 630),        # Ronald: 6:30PM to 7:30PM -> 570 to 630 minutes
        (5, "Richmond District", 15, 600, 720)   # Emily: 7:00PM to 9:00PM -> 600 to 720 minutes
    ]
    
    # Create Z3 variables
    s = [Int('s_%d' % i) for i in range(6)]   # start times for 6 activities (including start)
    meet_vars = [Bool('meet_%d' % i) for i in range(1,6)]  # boolean for meetings 1 to 5
    
    solver = Optimize()
    
    # Fix start time at Nob Hill to 0 (9:00 AM)
    solver.add(s[0] == 0)
    
    # Time window constraints for each meeting
    for idx in range(1, 6):
        loc, dur, win_start, win_end = activities[idx][1:5]
        # If meeting is scheduled, it must be within the time window
        solver.add(Implies(meet_vars[idx-1], 
                          And(s[idx] >= win_start, 
                              s[idx] + dur <= win_end)))
    
    # Disjunctive constraints for every pair of activities (including start)
    for i in range(6):
        loc_i = activities[i][1]
        dur_i = activities[i][2]
        for j in range(i+1, 6):
            loc_j = activities[j][1]
            dur_j = activities[j][2]
            
            travel_ij = travel_times[loc_i][loc_j]
            travel_ji = travel_times[loc_j][loc_i]
            
            # For start activity (index 0), it's always present
            meet_i = True if i == 0 else meet_vars[i-1]
            meet_j = True if j == 0 else meet_vars[j-1]
            
            # Either one of the meetings is not scheduled, or they are ordered with travel time
            solver.add(Or(
                Not(meet_i), 
                Not(meet_j),
                s[j] >= s[i] + dur_i + travel_ij,
                s[i] >= s[j] + dur_j + travel_ji
            ))
    
    # Maximize the number of meetings scheduled
    total_meet = Sum([If(var, 1, 0) for var in meet_vars])
    solver.maximize(total_meet)
    
    # Solve the model
    if solver.check() == sat:
        model = solver.model()
        scheduled_meetings = []
        person_map = {
            1: "Jeffrey",
            2: "Deborah",
            3: "Margaret",
            4: "Ronald",
            5: "Emily"
        }
        
        base_minutes = 9 * 60  # 9:00 AM in minutes from midnight
        
        for idx in range(1, 6):
            if model.eval(meet_vars[idx-1], model_completion=True):
                start_val = model.eval(s[idx], model_completion=True)
                if not isinstance(start_val, IntNumRef):
                    continue
                start_minutes = start_val.as_long()
                total_minutes = base_minutes + start_minutes
                hours = total_minutes // 60
                minutes = total_minutes % 60
                start_time_str = f"{hours:02d}:{minutes:02d}"
                
                end_minutes = total_minutes + activities[idx][2]
                hours_end = end_minutes // 60
                minutes_end = end_minutes % 60
                end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
                
                person = person_map[idx]
                scheduled_meetings.append({
                    "action": "meet",
                    "person": person,
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        result = {'itinerary': scheduled_meetings}
        print(json.dumps(result))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()