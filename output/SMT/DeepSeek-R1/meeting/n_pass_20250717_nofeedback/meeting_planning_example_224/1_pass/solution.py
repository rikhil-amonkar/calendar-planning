from z3 import *

def main():
    # Define meetings with their details
    meetings = [
        {"name": "Melissa", "location": "GG", "min_duration": 15, "available_start": -30, "available_end": 660},
        {"name": "Emily", "location": "Rich", "min_duration": 120, "available_start": 465, "available_end": 780},
        {"name": "Nancy", "location": "Pres", "min_duration": 105, "available_start": 645, "available_end": 780}
    ]
    
    # Travel times from Fisherman's Wharf (FW) to each location
    fw_travel = {
        "GG": 25,
        "Rich": 18,
        "Pres": 17
    }
    
    # Travel times between locations
    travel_times = {
        ("GG", "Rich"): 7,
        ("GG", "Pres"): 11,
        ("Rich", "GG"): 9,
        ("Rich", "Pres"): 7,
        ("Pres", "GG"): 12,
        ("Pres", "Rich"): 7
    }
    
    # Create solver and variables
    s = [Int(f's{i}') for i in range(3)]  # Start times for Melissa, Emily, Nancy
    first = Int('first')
    second = Int('second')
    third = Int('third')
    
    solver = Solver()
    
    # Order constraints: first, second, third must be distinct and in {0,1,2}
    solver.add(Distinct(first, second, third))
    solver.add(first >= 0, first <= 2)
    solver.add(second >= 0, second <= 2)
    solver.add(third >= 0, third <= 2)
    
    # Travel time from FW to the first meeting location
    travel_time0 = If(first == 0, fw_travel["GG"],
                      If(first == 1, fw_travel["Rich"],
                      fw_travel["Pres"]))
    
    # Constraint: start time of first meeting >= travel time from FW
    solver.add(If(first == 0, s[0] >= travel_time0,
                  If(first == 1, s[1] >= travel_time0,
                  s[2] >= travel_time0)))
    
    # Travel time from first to second meeting location
    def get_travel_time(idx1, idx2):
        loc1 = meetings[idx1]['location']
        loc2 = meetings[idx2]['location']
        return travel_times.get((loc1, loc2), 0)  # Default to 0 if same location (shouldn't happen)
    
    travel_time1 = If(And(first == 0, second == 1), get_travel_time(0, 1),
                      If(And(first == 0, second == 2), get_travel_time(0, 2),
                      If(And(first == 1, second == 0), get_travel_time(1, 0),
                      If(And(first == 1, second == 2), get_travel_time(1, 2),
                      If(And(first == 2, second == 0), get_travel_time(2, 0),
                      If(And(first == 2, second == 1), get_travel_time(2, 1), 0))))))
    
    # Constraint: start time of second meeting >= end time of first meeting + travel time
    min_duration_first = If(first == 0, meetings[0]['min_duration'],
                            If(first == 1, meetings[1]['min_duration'],
                            meetings[2]['min_duration']))
    
    solver.add(If(second == 0, 
                  s[0] >= If(first == 0, s[0] + min_duration_first,
                              If(first == 1, s[1] + min_duration_first,
                              s[2] + min_duration_first)) + travel_time1,
                If(second == 1,
                  s[1] >= If(first == 0, s[0] + min_duration_first,
                              If(first == 1, s[1] + min_duration_first,
                              s[2] + min_duration_first)) + travel_time1,
                  s[2] >= If(first == 0, s[0] + min_duration_first,
                              If(first == 1, s[1] + min_duration_first,
                              s[2] + min_duration_first)) + travel_time1)))
    
    # Travel time from second to third meeting location
    travel_time2 = If(And(second == 0, third == 1), get_travel_time(0, 1),
                      If(And(second == 0, third == 2), get_travel_time(0, 2),
                      If(And(second == 1, third == 0), get_travel_time(1, 0),
                      If(And(second == 1, third == 2), get_travel_time(1, 2),
                      If(And(second == 2, third == 0), get_travel_time(2, 0),
                      If(And(second == 2, third == 1), get_travel_time(2, 1), 0))))))
    
    # Constraint: start time of third meeting >= end time of second meeting + travel time
    min_duration_second = If(second == 0, meetings[0]['min_duration'],
                             If(second == 1, meetings[1]['min_duration'],
                             meetings[2]['min_duration']))
    
    solver.add(If(third == 0, 
                  s[0] >= If(second == 0, s[0] + min_duration_second,
                              If(second == 1, s[1] + min_duration_second,
                              s[2] + min_duration_second)) + travel_time2,
                If(third == 1,
                  s[1] >= If(second == 0, s[0] + min_duration_second,
                              If(second == 1, s[1] + min_duration_second,
                              s[2] + min_duration_second)) + travel_time2,
                  s[2] >= If(second == 0, s[0] + min_duration_second,
                              If(second == 1, s[1] + min_duration_second,
                              s[2] + min_duration_second)) + travel_time2)))
    
    # Individual meeting constraints
    # Melissa
    solver.add(s[0] >= meetings[0]['available_start'])
    solver.add(s[0] + meetings[0]['min_duration'] <= meetings[0]['available_end'])
    
    # Emily
    solver.add(s[1] >= meetings[1]['available_start'])
    solver.add(s[1] + meetings[1]['min_duration'] <= meetings[1]['available_end'])
    
    # Nancy
    solver.add(s[2] >= meetings[2]['available_start'])
    solver.add(s[2] + meetings[2]['min_duration'] <= meetings[2]['available_end'])
    
    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        s0_val = model.evaluate(s[0]).as_long()
        s1_val = model.evaluate(s[1]).as_long()
        s2_val = model.evaluate(s[2]).as_long()
        
        # Convert minutes to time strings
        def min_to_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            # Adjust for negative minutes (if any)
            if hours < 0:
                hours += 24
            return f"{hours:02d}:{mins:02d}"
        
        # Calculate end times
        e0_val = s0_val + meetings[0]['min_duration']
        e1_val = s1_val + meetings[1]['min_duration']
        e2_val = s2_val + meetings[2]['min_duration']
        
        # Create itinerary
        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": min_to_time(s0_val), "end_time": min_to_time(e0_val)},
            {"action": "meet", "person": "Emily", "start_time": min_to_time(s1_val), "end_time": min_to_time(e1_val)},
            {"action": "meet", "person": "Nancy", "start_time": min_to_time(s2_val), "end_time": min_to_time(e2_val)}
        ]
        
        # Output the solution in JSON format
        print('SOLUTION:')
        print('{"itinerary": ' + json.dumps(itinerary) + '}')
    else:
        print("No solution found")

if __name__ == "__main__":
    import json
    main()