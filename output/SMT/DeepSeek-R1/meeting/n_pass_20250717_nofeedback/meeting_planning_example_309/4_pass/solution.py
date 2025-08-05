from z3 import *
import json

def min_to_time(minutes):
    h = 9 + minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Precomputed travel times (minutes)
    travel_FD_to = {
        "Nancy": 5,    # FD -> Chinatown
        "Mary": 17,    # FD -> Alamo Square
        "Jessica": 19  # FD -> Bayview
    }
    
    travel_between = {
        ("Nancy", "Mary"): 17,
        ("Nancy", "Jessica"): 22,
        ("Mary", "Nancy"): 16,
        ("Mary", "Jessica"): 16,
        ("Jessica", "Nancy"): 18,
        ("Jessica", "Mary"): 16
    }
    
    # Meeting data
    names = ["Nancy", "Mary", "Jessica"]
    durations = [90, 75, 45]  # minutes
    min_starts = [30, 0, 135]  # minutes after 9:00 AM
    max_ends = [270, 720, 285]  # minutes after 9:00 AM
    
    s = Solver()
    
    # Meeting order variables (0=Nancy, 1=Mary, 2=Jessica)
    first = Int('first')
    second = Int('second')
    third = Int('third')
    
    # Start time variables (minutes after 9:00 AM)
    s0 = Int('s0')  # first meeting start
    s1 = Int('s1')  # second meeting start
    s2 = Int('s2')  # third meeting start
    
    # Constraints for meeting indices
    s.add(Distinct(first, second, third))
    s.add(first >= 0, first <= 2)
    s.add(second >= 0, second <= 2)
    s.add(third >= 0, third <= 2)
    
    # Travel time expressions
    travel0 = If(first == 0, travel_FD_to["Nancy"],
                If(first == 1, travel_FD_to["Mary"],
                travel_FD_to["Jessica"]))
    
    travel1 = If(And(first == 0, second == 1), travel_between[("Nancy", "Mary")],
                If(And(first == 0, second == 2), travel_between[("Nancy", "Jessica")],
                If(And(first == 1, second == 0), travel_between[("Mary", "Nancy")],
                If(And(first == 1, second == 2), travel_between[("Mary", "Jessica")],
                If(And(first == 2, second == 0), travel_between[("Jessica", "Nancy")],
                travel_between[("Jessica", "Mary")])))))
    
    travel2 = If(And(second == 0, third == 1), travel_between[("Nancy", "Mary")],
                If(And(second == 0, third == 2), travel_between[("Nancy", "Jessica")],
                If(And(second == 1, third == 0), travel_between[("Mary", "Nancy")],
                If(And(second == 1, third == 2), travel_between[("Mary", "Jessica")],
                If(And(second == 2, third == 0), travel_between[("Jessica", "Nancy")],
                travel_between[("Jessica", "Mary")])))))
    
    # Meeting constraints using If expressions
    min_start0 = If(first == 0, min_starts[0],
                   If(first == 1, min_starts[1],
                   min_starts[2]))
    
    max_end0 = If(first == 0, max_ends[0],
                 If(first == 1, max_ends[1],
                 max_ends[2]))
    
    duration0 = If(first == 0, durations[0],
                  If(first == 1, durations[1],
                  durations[2]))
    
    min_start1 = If(second == 0, min_starts[0],
                   If(second == 1, min_starts[1],
                   min_starts[2]))
    
    max_end1 = If(second == 0, max_ends[0],
                 If(second == 1, max_ends[1],
                 max_ends[2]))
    
    duration1 = If(second == 0, durations[0],
                  If(second == 1, durations[1],
                  durations[2]))
    
    min_start2 = If(third == 0, min_starts[0],
                   If(third == 1, min_starts[1],
                   min_starts[2]))
    
    max_end2 = If(third == 0, max_ends[0],
                 If(third == 1, max_ends[1],
                 max_ends[2]))
    
    duration2 = If(third == 0, durations[0],
                  If(third == 1, durations[1],
                  durations[2]))
    
    # First meeting constraints
    s.add(s0 >= travel0)
    s.add(s0 >= min_start0)
    s.add(s0 + duration0 <= max_end0)
    
    # Second meeting constraints
    s.add(s1 >= s0 + duration0 + travel1)
    s.add(s1 >= min_start1)
    s.add(s1 + duration1 <= max_end1)
    
    # Third meeting constraints
    s.add(s2 >= s1 + duration1 + travel2)
    s.add(s2 >= min_start2)
    s.add(s2 + duration2 <= max_end2)
    
    if s.check() == sat:
        m = s.model()
        first_val = m[first].as_long()
        second_val = m[second].as_long()
        third_val = m[third].as_long()
        s0_val = m[s0].as_long()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        
        # Create meeting entries
        meetings = [
            {"person": names[first_val], "start": s0_val, "end": s0_val + durations[first_val]},
            {"person": names[second_val], "start": s1_val, "end": s1_val + durations[second_val]},
            {"person": names[third_val], "start": s2_val, "end": s2_val + durations[third_val]}
        ]
        
        # Sort by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Build itinerary
        itinerary = []
        for meet in meetings:
            itinerary.append({
                "action": "meet",
                "person": meet["person"],
                "start_time": min_to_time(meet["start"]),
                "end_time": min_to_time(meet["end"])
            })
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()