from z3 import *
import json

def main():
    # Convert time string to minutes since 9:00 AM
    def time_to_minutes(s):
        parts = s[:-2].split(':')
        h = int(parts[0])
        m = int(parts[1])
        if s.endswith('PM') and h != 12:
            h += 12
        if s.endswith('AM') and h == 12:
            h = 0
        return h * 60 + m - 540  # Subtract 9:00 AM (540 minutes)

    # Build travel time dictionary
    travel_times = {
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "North Beach"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "North Beach"): 23,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "North Beach"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "North Beach"): 28,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "North Beach"): 8,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Nob Hill"): 7
    }

    # Define meetings (excluding Kevin)
    meetings = [
        {"name": "Michelle", "location": "Golden Gate Park", "start_avail": time_to_minutes("8:00PM"), "end_avail": time_to_minutes("9:00PM"), "min_dur": 15},
        {"name": "Emily", "location": "Fisherman's Wharf", "start_avail": time_to_minutes("4:15PM"), "end_avail": time_to_minutes("7:00PM"), "min_dur": 30},
        {"name": "Mark", "location": "Marina District", "start_avail": time_to_minutes("6:15PM"), "end_avail": time_to_minutes("7:45PM"), "min_dur": 75},
        {"name": "Barbara", "location": "Alamo Square", "start_avail": time_to_minutes("5:00PM"), "end_avail": time_to_minutes("7:00PM"), "min_dur": 120},
        {"name": "Laura", "location": "Sunset District", "start_avail": time_to_minutes("7:00PM"), "end_avail": time_to_minutes("9:15PM"), "min_dur": 75},
        {"name": "Mary", "location": "Nob Hill", "start_avail": time_to_minutes("5:30PM"), "end_avail": time_to_minutes("7:00PM"), "min_dur": 45},
        {"name": "Helen", "location": "North Beach", "start_avail": time_to_minutes("11:00AM"), "end_avail": time_to_minutes("12:15PM"), "min_dur": 45}
    ]
    
    n = len(meetings)
    s = Optimize()
    
    # Create variables for each meeting
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    attended = [Bool(f"attended_{i}") for i in range(n)]
    
    # Meeting constraints
    for i in range(n):
        m = meetings[i]
        s.add(Implies(attended[i], start[i] >= max(0, m["start_avail"])))
        s.add(Implies(attended[i], end[i] <= m["end_avail"]))
        s.add(Implies(attended[i], end[i] - start[i] >= m["min_dur"]))
        s.add(Implies(attended[i], start[i] >= travel_times[("Presidio", m["location"])]))
    
    # Disjunctive constraints for all meeting pairs
    for i in range(n):
        for j in range(i+1, n):
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_ij = travel_times[(loc_i, loc_j)]
            travel_ji = travel_times[(loc_j, loc_i)]
            s.add(Implies(And(attended[i], attended[j]), 
                          Or(end[i] + travel_ij <= start[j], 
                             end[j] + travel_ji <= start[i])))
    
    # Maximize number of meetings
    total_meetings = Sum([If(attended[i], 1, 0) for i in range(n)])
    s.maximize(total_meetings)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n):
            if model.eval(attended[i]):
                start_val = model.eval(start[i]).as_long()
                end_val = model.eval(end[i]).as_long()
                total_start = 540 + start_val
                total_end = 540 + end_val
                h_start = total_start // 60
                m_start = total_start % 60
                h_end = total_end // 60
                m_end = total_end % 60
                start_str = f"{h_start}:{m_start:02d}"
                end_str = f"{h_end}:{m_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": meetings[i]["location"],
                    "person": meetings[i]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        itinerary.sort(key=lambda x: x["start_time"])
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()