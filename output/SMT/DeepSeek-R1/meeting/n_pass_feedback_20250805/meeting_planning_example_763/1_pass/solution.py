from z3 import *

def main():
    # Define location names
    locations = [
        "Chinatown",
        "Embarcadero",
        "Pacific Heights",
        "Russian Hill",
        "Haight-Ashbury",
        "Golden Gate Park",
        "Fisherman's Wharf",
        "Sunset District",
        "The Castro"
    ]
    
    # Travel times dictionary
    travel_times_dict = {
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "The Castro"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "The Castro"): 17,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Sunset District"): 17
    }
    
    # Build travel_time matrix (9x9)
    travel_time = [[0]*9 for _ in range(9)]
    for i in range(9):
        for j in range(9):
            if i != j:
                key = (locations[i], locations[j])
                travel_time[i][j] = travel_times_dict[key]
    
    # Define meetings: virtual meeting (index0) and real meetings (index1 to 8)
    meetings = [
        {"name": "start", "loc": 0, "window": (0, 0), "dur": 0},  # virtual meeting at Chinatown
        {"name": "Richard", "loc": 1, "window": (375, 585), "dur": 90},  # 3:15PM to 6:45PM
        {"name": "Mark", "loc": 2, "window": (360, 480), "dur": 45},     # 3:00PM to 5:00PM
        {"name": "Matthew", "loc": 3, "window": (510, 720), "dur": 90},  # 5:30PM to 9:00PM
        {"name": "Rebecca", "loc": 4, "window": (345, 540), "dur": 60},  # 2:45PM to 6:00PM
        {"name": "Melissa", "loc": 5, "window": (285, 510), "dur": 90},  # 1:45PM to 5:30PM
        {"name": "Margaret", "loc": 6, "window": (345, 675), "dur": 15}, # 2:45PM to 8:15PM
        {"name": "Emily", "loc": 7, "window": (405, 480), "dur": 45},    # 3:45PM to 5:00PM
        {"name": "George", "loc": 8, "window": (300, 435), "dur": 75}    # 2:00PM to 4:15PM
    ]
    n = len(meetings)  # total meetings including virtual (n=9)
    
    # Create Z3 variables
    attend = [Bool(f"attend_{i}") for i in range(n)]
    start = [Real(f"start_{i}") for i in range(n)]
    end = [Real(f"end_{i}") for i in range(n)]
    
    # Create before matrix (n x n)
    before = [[None if i == j else Bool(f"before_{i}_{j}") for j in range(n)] for i in range(n)]
    
    s = Solver()
    opt = Optimize()
    
    # Fix virtual meeting (index0)
    s.add(attend[0] == True)
    s.add(start[0] == 0)
    s.add(end[0] == 0)
    
    # Constraints for real meetings (indices 1 to 8)
    for i in range(1, n):
        # If attended, enforce time window and duration
        s.add(Implies(attend[i], 
                      And(start[i] >= meetings[i]["window"][0], 
                          end[i] == start[i] + meetings[i]["dur"],
                          end[i] <= meetings[i]["window"][1])))
        # Ensure start times are integers (as travel times and durations are integers)
        s.add(ToInt(start[i]) == start[i])
    
    # Constraints for the before matrix and travel times
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # If both meetings are attended, enforce ordering and travel time
            s.add(Implies(And(attend[i], attend[j]),
                          And(Or(before[i][j], before[j][i]), 
                              Not(And(before[i][j], before[j][i]))))
            s.add(Implies(And(attend[i], attend[j], before[i][j]),
                          end[i] + travel_time[meetings[i]["loc"]][meetings[j]["loc"]] <= start[j]))
    
    # Maximize the number of attended real meetings (indices 1 to 8)
    objective = Sum([If(attend[i], 1, 0) for i in range(1, n)])
    opt.add(s.assertions())
    opt.maximize(objective)
    
    if opt.check() == sat:
        model = opt.model()
        # Extract attended meetings
        itinerary = []
        for i in range(1, n):
            if model.eval(attend[i], model_completion=True):
                start_val = model.eval(start[i], model_completion=True)
                end_val = model.eval(end[i], model_completion=True)
                # Convert Z3 values to integers
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                # Convert minutes to time string (from 9:00 AM)
                def min_to_time(m):
                    total_minutes = 9 * 60 + m
                    hours = total_minutes // 60
                    minutes = total_minutes % 60
                    return f"{hours:02d}:{minutes:02d}"
                start_time_str = min_to_time(start_min)
                end_time_str = min_to_time(end_min)
                itinerary.append({
                    "action": "meet",
                    "person": meetings[i]["name"],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        # Output the solution in the required JSON format
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()