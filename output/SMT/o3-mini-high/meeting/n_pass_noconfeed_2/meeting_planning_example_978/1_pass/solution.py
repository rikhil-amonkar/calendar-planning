from z3 import *
import json

def minutes_to_time_str(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def main():
    # Define friend meeting constraints
    # Times are in minutes after midnight.
    # 9:00 AM = 540, etc.
    friends = [
        {"name": "Stephanie", "location": "Fisherman's Wharf", "a_start": 930, "a_end": 1320, "min_dur": 30},
        {"name": "Lisa", "location": "Financial District", "a_start": 645, "a_end": 1035, "min_dur": 15},
        {"name": "Melissa", "location": "Russian Hill", "a_start": 1020, "a_end": 1305, "min_dur": 120},
        {"name": "Betty", "location": "Marina District", "a_start": 645, "a_end": 855, "min_dur": 60},
        {"name": "Sarah", "location": "Richmond District", "a_start": 975, "a_end": 1170, "min_dur": 105},
        {"name": "Daniel", "location": "Pacific Heights", "a_start": 1110, "a_end": 1305, "min_dur": 60},
        {"name": "Joshua", "location": "Haight-Ashbury", "a_start": 540, "a_end": 930, "min_dur": 15},
        {"name": "Joseph", "location": "Presidio", "a_start": 420, "a_end": 780, "min_dur": 45},
        {"name": "Andrew", "location": "Nob Hill", "a_start": 1185, "a_end": 1320, "min_dur": 105},
        {"name": "John", "location": "The Castro", "a_start": 795, "a_end": 1185, "min_dur": 45}
    ]
    
    # Define travel times (in minutes) as provided.
    # Note: travel times are directional.
    travel = {
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,
        
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "The Castro"): 27,
        
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "The Castro"): 20,
        
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "The Castro"): 21,
        
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "The Castro"): 22,
        
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "The Castro"): 16,
        
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "The Castro"): 16,
        
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "The Castro"): 21,
        
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "The Castro"): 17,
        
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Nob Hill"): 16
    }
    
    # Create an optimizer instance
    opt = Optimize()
    N = len(friends)
    
    # For each friend, create SMT variables:
    # scheduled: whether to meet this friend
    # start, end: meeting start and end times (in minutes after midnight)
    # order: position in the sequence (1 = first meeting, etc. 0 when not scheduled)
    scheduled = [Bool(f"scheduled_{i}") for i in range(N)]
    start_vars = [Int(f"start_{i}") for i in range(N)]
    end_vars = [Int(f"end_{i}") for i in range(N)]
    order_vars = [Int(f"order_{i}") for i in range(N)]
    
    # Domain constraints for order: if scheduled then order in [1, N], else order is 0.
    for i in range(N):
        opt.add(If(scheduled[i], And(order_vars[i] >= 1, order_vars[i] <= N), order_vars[i] == 0))
    
    # Ensure that scheduled meetings have unique order values.
    for i in range(N):
        for j in range(i+1, N):
            opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))
    
    # Meeting availability and duration constraints
    for i in range(N):
        f = friends[i]
        opt.add(Implies(scheduled[i], start_vars[i] >= f["a_start"]))
        opt.add(Implies(scheduled[i], end_vars[i] <= f["a_end"]))
        opt.add(Implies(scheduled[i], end_vars[i] - start_vars[i] >= f["min_dur"]))
        opt.add(Implies(scheduled[i], end_vars[i] >= start_vars[i]))
        # Ensure times are within a valid day (0 to 1440 minutes)
        opt.add(start_vars[i] >= 0, start_vars[i] <= 1440)
        opt.add(end_vars[i] >= 0, end_vars[i] <= 1440)
    
    # For the first scheduled meeting (order == 1), enforce travel from starting point.
    # You arrive at Embarcadero at 9:00 (540).
    for i in range(N):
        opt.add(Implies(And(scheduled[i], order_vars[i] == 1),
                        start_vars[i] >= 540 + travel[("Embarcadero", friends[i]["location"])]))
    
    # For meetings with order > 1, enforce that each such meeting is reached from
    # the immediately preceding meeting.
    for i in range(N):
        for j in range(N):
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] == order_vars[j] + 1),
                            start_vars[i] >= end_vars[j] + travel[(friends[j]["location"], friends[i]["location"])]))
    
    # Enforce that meeting order implies increasing start times.
    for i in range(N):
        for j in range(N):
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                            start_vars[i] < start_vars[j]))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(N)])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(N):
            if is_true(model.evaluate(scheduled[i])):
                order_val = model.evaluate(order_vars[i]).as_long()
                s_time = model.evaluate(start_vars[i]).as_long()
                e_time = model.evaluate(end_vars[i]).as_long()
                scheduled_meetings.append((order_val, s_time, e_time, friends[i]["location"], friends[i]["name"]))
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = []
        for om in scheduled_meetings:
            _, s, e, location, person = om
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time_str(s),
                "end_time": minutes_to_time_str(e)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
    
if __name__ == "__main__":
    main()