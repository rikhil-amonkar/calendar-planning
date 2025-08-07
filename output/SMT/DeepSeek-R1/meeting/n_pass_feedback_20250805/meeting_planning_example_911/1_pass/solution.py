from z3 import *
import json

def main():
    # Define the meetings: 0 to 10 (0 is the start at The Castro)
    n_meetings = 11
    loc = [
        'The Castro',           #0
        'Haight-Ashbury',       #1: Stephanie
        'Nob Hill',             #2: Nancy
        'Marina District',      #3: David
        'Union Square',         #4: Elizabeth
        'Financial District',   #5: Robert
        'Embarcadero',          #6: Brian
        'Presidio',             #7: James
        'Richmond District',    #8: Melissa
        'Golden Gate Park',     #9: Sarah
        'North Beach'           #10: Steven
    ]
    
    # Data for friends: [ (available_start_min, available_end_min, min_duration_min) ]
    data = [
        None,  # dummy for index0
        (10*60+15, 12*60+15, 75),    #1: Stephanie
        (8*60+15, 12*60+45, 90),     #2: Nancy
        (11*60+15, 13*60+15, 120),   #3: David
        (11*60+30, 21*60, 60),        #4: Elizabeth
        (13*60+15, 15*60+15, 45),     #5: Robert
        (14*60+15, 16*60, 105),       #6: Brian
        (15*60, 18*60+15, 120),       #7: James
        (14*60, 19*60+30, 30),        #8: Melissa
        (17*60, 19*60+15, 75),        #9: Sarah
        (17*60+30, 20*60+30, 15)      #10: Steven
    ]
    
    names = [
        None,  # dummy for index0
        'Stephanie',  #1
        'Nancy',      #2
        'David',      #3
        'Elizabeth',  #4
        'Robert',     #5
        'Brian',      #6
        'James',      #7
        'Melissa',    #8
        'Sarah',      #9
        'Steven'      #10
    ]
    
    # Travel times dictionary
    travel_times_dict = {
        'The Castro': {
            'North Beach': 20,
            'Golden Gate Park': 11,
            'Embarcadero': 22,
            'Haight-Ashbury': 6,
            'Richmond District': 16,
            'Nob Hill': 16,
            'Marina District': 21,
            'Presidio': 20,
            'Union Square': 19,
            'Financial District': 21
        },
        'North Beach': {
            'The Castro': 23,
            'Golden Gate Park': 22,
            'Embarcadero': 6,
            'Haight-Ashbury': 18,
            'Richmond District': 18,
            'Nob Hill': 7,
            'Marina District': 9,
            'Presidio': 17,
            'Union Square': 7,
            'Financial District': 8
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'North Beach': 23,
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            'Richmond District': 7,
            'Nob Hill': 20,
            'Marina District': 16,
            'Presidio': 11,
            'Union Square': 22,
            'Financial District': 26
        },
        'Embarcadero': {
            'The Castro': 25,
            'North Beach': 5,
            'Golden Gate Park': 25,
            'Haight-Ashbury': 21,
            'Richmond District': 21,
            'Nob Hill': 10,
            'Marina District': 12,
            'Presidio': 20,
            'Union Square': 10,
            'Financial District': 5
        },
        'Haight-Ashbury': {
            'The Castro': 6,
            'North Beach': 19,
            'Golden Gate Park': 7,
            'Embarcadero': 20,
            'Richmond District': 10,
            'Nob Hill': 15,
            'Marina District': 17,
            'Presidio': 15,
            'Union Square': 19,
            'Financial District': 21
        },
        'Richmond District': {
            'The Castro': 16,
            'North Beach': 17,
            'Golden Gate Park': 9,
            'Embarcadero': 19,
            'Haight-Ashbury': 10,
            'Nob Hill': 17,
            'Marina District': 9,
            'Presidio': 7,
            'Union Square': 21,
            'Financial District': 22
        },
        'Nob Hill': {
            'The Castro': 17,
            'North Beach': 8,
            'Golden Gate Park': 17,
            'Embarcadero': 9,
            'Haight-Ashbury': 13,
            'Richmond District': 14,
            'Marina District': 11,
            'Presidio': 17,
            'Union Square': 7,
            'Financial District': 9
        },
        'Marina District': {
            'The Castro': 22,
            'North Beach': 11,
            'Golden Gate Park': 18,
            'Embarcadero': 14,
            'Haight-Ashbury': 16,
            'Richmond District': 11,
            'Nob Hill': 12,
            'Presidio': 10,
            'Union Square': 16,
            'Financial District': 17
        },
        'Presidio': {
            'The Castro': 21,
            'North Beach': 18,
            'Golden Gate Park': 12,
            'Embarcadero': 20,
            'Haight-Ashbury': 15,
            'Richmond District': 7,
            'Nob Hill': 18,
            'Marina District': 11,
            'Union Square': 22,
            'Financial District': 23
        },
        'Union Square': {
            'The Castro': 17,
            'North Beach': 10,
            'Golden Gate Park': 22,
            'Embarcadero': 11,
            'Haight-Ashbury': 18,
            'Richmond District': 20,
            'Nob Hill': 9,
            'Marina District': 18,
            'Presidio': 24,
            'Financial District': 9
        },
        'Financial District': {
            'The Castro': 20,
            'North Beach': 7,
            'Golden Gate Park': 23,
            'Embarcadero': 4,
            'Haight-Ashbury': 19,
            'Richmond District': 21,
            'Nob Hill': 8,
            'Marina District': 15,
            'Presidio': 22,
            'Union Square': 9
        }
    }
    
    # Create Z3 variables
    met = [None] * n_meetings
    start = [None] * n_meetings
    duration = [None] * n_meetings
    
    # Meeting 0 (start) is fixed
    met[0] = True
    start[0] = 540   # 9:00 AM in minutes
    duration[0] = 0
    
    # For meetings 1 to 10
    for i in range(1, n_meetings):
        met[i] = Bool(f'met_{i}')
        start[i] = Int(f'start_{i}')
        duration[i] = Int(f'duration_{i}')
    
    s = Solver()
    
    # Time window constraints for friends 1 to 10
    for i in range(1, n_meetings):
        avail_start, avail_end, min_dur = data[i]
        s.add(Implies(met[i], start[i] >= avail_start))
        s.add(Implies(met[i], start[i] + duration[i] <= avail_end))
        s.add(Implies(met[i], duration[i] >= min_dur))
        # Also set bounds to help the solver
        s.add(start[i] >= 540)  # not earlier than 9:00 AM
        s.add(start[i] <= 20*60+30)  # not later than Steven's end time (8:30 PM)
        s.add(duration[i] >= 0)
        s.add(duration[i] <= (avail_end - avail_start))  # maximum possible duration
    
    # Fixed meetings for David (index3) and Brian (index6)
    s.add(Implies(met[3], And(start[3] == 11*60+15, duration[3] == 120)))
    s.add(Implies(met[6], And(start[6] == 14*60+15, duration[6] == 105)))
    
    # Pairwise constraints for every pair of meetings (including start)
    for i in range(0, n_meetings):
        for j in range(i+1, n_meetings):
            active_i = met[i] if i > 0 else True
            active_j = met[j] if j > 0 else True
            # If both are active, add disjunctive constraint
            constraint = Or(
                start[i] >= start[j] + duration[j] + travel_times_dict[loc[j]][loc[i]],
                start[j] >= start[i] + duration[i] + travel_times_dict[loc[i]][loc[j]]
            )
            s.add(Implies(And(active_i, active_j), constraint))
    
    # Maximize the number of meetings
    opt = Optimize()
    opt.add(s.assertions())
    num_meetings = Sum([If(met[i], 1, 0) for i in range(1, n_meetings)])
    opt.maximize(num_meetings)
    
    itinerary = []
    if opt.check() == sat:
        m = opt.model()
        # Collect all scheduled meetings
        for i in range(1, n_meetings):
            if is_true(m.eval(met[i])):
                start_val = m.eval(start[i])
                dur_val = m.eval(duration[i])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = start_val
                if isinstance(dur_val, IntNumRef):
                    dur_min = dur_val.as_long()
                else:
                    dur_min = dur_val
                end_min = start_min + dur_min
                # Format as HH:MM
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
    else:
        # If no solution, return empty itinerary
        itinerary = []
    
    # Output the result
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()