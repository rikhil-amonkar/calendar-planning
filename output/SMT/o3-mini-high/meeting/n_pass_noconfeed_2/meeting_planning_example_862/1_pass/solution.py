import json
from z3 import *

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Meeting data: person, location, available start, available end, minimum meeting duration (in minutes)
    meetings = [
        {"person": "Laura", "location": "Alamo Square", "win_start": 870, "win_end": 975, "min_duration": 75},
        {"person": "Brian", "location": "Presidio", "win_start": 615, "win_end": 1020, "min_duration": 30},
        {"person": "Karen", "location": "Russian Hill", "win_start": 1080, "win_end": 1215, "min_duration": 90},
        {"person": "Stephanie", "location": "North Beach", "win_start": 615, "win_end": 960, "min_duration": 75},
        {"person": "Helen", "location": "Golden Gate Park", "win_start": 690, "win_end": 1305, "min_duration": 120},
        {"person": "Sandra", "location": "Richmond District", "win_start": 480, "win_end": 915, "min_duration": 30},
        {"person": "Mary", "location": "Embarcadero", "win_start": 1005, "win_end": 1125, "min_duration": 120},
        {"person": "Deborah", "location": "Financial District", "win_start": 1140, "win_end": 1245, "min_duration": 105},
        {"person": "Elizabeth", "location": "Marina District", "win_start": 510, "win_end": 795, "min_duration": 105}
    ]
    
    # Travel times in minutes between locations (source, destination): time in minutes
    travel_times = {
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Marina District"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Marina District"): 16,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Marina District"): 9,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17
    }
    
    n = len(meetings)
    # Create Optimize solver instance (for optimization over schedules)
    opt = Optimize()

    # Create decision variables for each meeting:
    # attend: Boolean, true if the meeting is scheduled
    # order_vars: integer order in the sequence (0 if not scheduled, >=1 if scheduled)
    # start_vars and end_vars: meeting start and end times (in minutes from midnight)
    attend = [Bool(f"attend_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    
    # Add constraints for each meeting based on availability and minimum duration.
    for i in range(n):
        m = meetings[i]
        # Order variable is 0 if not attended, or between 1 and n if attended.
        opt.add(order_vars[i] >= 0, order_vars[i] <= n)
        opt.add(Implies(attend[i], order_vars[i] >= 1))
        opt.add(Implies(Not(attend[i]), order_vars[i] == 0))
        opt.add(Implies(attend[i], start_vars[i] >= m["win_start"]))
        opt.add(Implies(attend[i], end_vars[i] <= m["win_end"]))
        opt.add(Implies(attend[i], end_vars[i] - start_vars[i] >= m["min_duration"]))
        opt.add(Implies(attend[i], start_vars[i] < end_vars[i]))
    
    # Ensure that if two meetings are scheduled, they must have distinct order numbers.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(attend[i], attend[j]), order_vars[i] != order_vars[j]))
    
    # Ensure order continuity: if a meeting has order > 1 then some meeting must have order one less.
    for i in range(n):
        opt.add(Implies(And(attend[i], order_vars[i] > 1),
                        Or([And(attend[j], order_vars[j] == order_vars[i] - 1)
                            for j in range(n) if j != i])))
    
    # Travel constraints:
    # You start at Mission District at 9:00 (9:00 = 9*60 = 540 minutes).
    start_location = "Mission District"
    arrival_time = 540
    # For the first meeting in the sequence, include travel time from starting location.
    for i in range(n):
        m = meetings[i]
        travel_time = travel_times.get((start_location, m["location"]), 0)
        opt.add(Implies(And(attend[i], order_vars[i] == 1),
                        start_vars[i] >= arrival_time + travel_time))
    
    # For consecutive meetings, enforce that the next meeting starts after the previous one finishes plus travel.
    for i in range(n):
        for j in range(n):
            if i != j:
                travel_time = travel_times.get((meetings[j]["location"], meetings[i]["location"]), 0)
                opt.add(Implies(And(attend[i], attend[j], order_vars[i] == order_vars[j] + 1),
                                start_vars[i] >= end_vars[j] + travel_time))
    
    # Objective: maximize the total number of meetings attended.
    opt.maximize(Sum([If(attend[i], 1, 0) for i in range(n)]))
    
    if opt.check() == sat:
        model = opt.model()
        # Gather scheduled meetings along with their order.
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(attend[i])):
                scheduled.append((model.evaluate(order_vars[i]).as_long(), i))
        # Sort meetings by their order in the itinerary.
        scheduled.sort(key=lambda x: x[0])
        
        itinerary = []
        for order_val, i in scheduled:
            start_time = model.evaluate(start_vars[i]).as_long()
            end_time = model.evaluate(end_vars[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": meetings[i]["location"],
                "person": meetings[i]["person"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
        
if __name__ == "__main__":
    main()