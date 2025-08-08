from z3 import *
import json

def main():
    meetings_info = [
        (1, "Kevin", "Mission District", 165, 225, 60),
        (2, "Mark", "Fisherman's Wharf", 495, 660, 90),
        (3, "Jessica", "Russian Hill", 0, 360, 120),
        (4, "Jason", "Marina District", 375, 765, 120),
        (5, "John", "North Beach", 45, 540, 15),
        (6, "Karen", "Chinatown", 465, 600, 75),
        (7, "Sarah", "Pacific Heights", 510, 555, 45),
        (8, "Amanda", "The Castro", 660, 735, 60),
        (9, "Nancy", "Nob Hill", 45, 240, 45),
        (10, "Rebecca", "Sunset District", -15, 360, 75)
    ]
    
    travel_dict = {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Sunset District"): 24,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Sunset District"): 23,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Sunset District"): 27,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Mission District"): 17,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Sunset District"): 29,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Sunset District"): 21,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Sunset District"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Sunset District"): 24,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Nob Hill"): 27
    }
    
    s = Optimize()
    n_meetings = len(meetings_info)
    
    meet = [Bool(f"meet_{i}") for i in range(n_meetings)]
    start = [Int(f"start_{i}") for i in range(n_meetings)]
    end = [Int(f"end_{i}") for i in range(n_meetings)]
    travel_time = [Int(f"travel_{i}") for i in range(n_meetings)]
    prev_meeting = [Int(f"prev_{i}") for i in range(n_meetings)]
    first_meeting = Int("first_meeting")
    last_meeting = Int("last_meeting")
    
    # Meeting constraints
    for i in range(n_meetings):
        idx, name, loc, avail_start, avail_end, dur = meetings_info[i]
        # If meeting is scheduled, enforce availability and duration
        s.add(Implies(meet[i], start[i] >= avail_start))
        s.add(Implies(meet[i], end[i] == start[i] + dur))
        s.add(Implies(meet[i], end[i] <= avail_end))
        # Travel time for first meeting
        s.add(Implies(And(meet[i], prev_meeting[i] == -1), 
                      start[i] >= travel_dict[("Union Square", loc)]))
        # Travel time for subsequent meetings
        for j in range(n_meetings):
            if i != j:
                loc_i = meetings_info[i][2]
                loc_j = meetings_info[j][2]
                s.add(Implies(And(meet[i], meet[j], prev_meeting[i] == j),
                          start[i] >= end[j] + travel_dict[(loc_j, loc_i)]))
    
    # Ordering constraints
    for i in range(n_meetings):
        s.add(prev_meeting[i] >= -1)
        s.add(prev_meeting[i] < n_meetings)
        s.add(Implies(meet[i], prev_meeting[i] != i))
        s.add(Implies(Not(meet[i]), prev_meeting[i] == -2))
    
    # First meeting has prev = -1
    s.add(Or([And(meet[i], prev_meeting[i] == -1) for i in range(n_meetings)] + [Not(Or(meet))]))
    
    # Only one meeting has prev = -1
    s.add(Sum([If(And(meet[i], prev_meeting[i] == -1), 1, 0) for i in range(n_meetings)]) <= 1)
    
    # Each meeting can be predecessor to at most one other
    for i in range(n_meetings):
        s.add(Sum([If(And(meet[j], prev_meeting[j] == i), 1, 0) for j in range(n_meetings)]) <= 1)
    
    # Chain integrity
    for i in range(n_meetings):
        s.add(Implies(meet[i], 
                      Or(prev_meeting[i] == -1, 
                         Or([And(meet[j], prev_meeting[i] == j) for j in range(n_meetings) if j != i]))))
    
    # No cycles
    for i in range(n_meetings):
        s.add(Implies(meet[i], prev_meeting[i] != i))
        for j in range(n_meetings):
            if i != j:
                s.add(Implies(And(meet[i], meet[j], prev_meeting[i] == j), 
                              prev_meeting[j] != i))
    
    # Maximize number of meetings
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n_meetings)])
    s.maximize(total_meetings)
    
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        current = None
        # Find the first meeting
        for i in range(n_meetings):
            if m.evaluate(meet[i]) and m.evaluate(prev_meeting[i]) == -1:
                current = i
                break
                
        # Traverse the chain
        while current is not None:
            if m.evaluate(meet[current]):
                start_val = m.evaluate(start[current])
                end_val = m.evaluate(end[current])
                if is_int_value(start_val) and is_int_value(end_val):
                    start_min = start_val.as_long()
                    end_min = end_val.as_long()
                    total_start_min = 540 + start_min
                    total_end_min = 540 + end_min
                    start_hour = total_start_min // 60
                    start_minute = total_start_min % 60
                    end_hour = total_end_min // 60
                    end_minute = total_end_min % 60
                    start_time = f"{start_hour}:{start_minute:02d}"
                    end_time = f"{end_hour}:{end_minute:02d}"
                    name = meetings_info[current][1]
                    scheduled_meetings.append({
                        "action": "meet",
                        "person": name,
                        "start_time": start_time,
                        "end_time": end_time
                    })
            next_meeting = None
            for i in range(n_meetings):
                if i != current and m.evaluate(meet[i]) and m.evaluate(prev_meeting[i]) == current:
                    next_meeting = i
                    break
            current = next_meeting
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": scheduled_meetings}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

def is_int_value(v):
    return isinstance(v, IntNumRef)

if __name__ == "__main__":
    main()