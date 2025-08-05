from z3 import *
import json

def min_to_time(minutes):
    h = 9 + minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Define locations: 0=FD, 1=CT, 2=AS, 3=BV
    travel_matrix = [
        [0, 5, 17, 19],  # FD to [FD, CT, AS, BV]
        [5, 0, 17, 22],  # CT to [FD, CT, AS, BV]
        [17, 16, 0, 16], # AS to [FD, CT, AS, BV]
        [19, 18, 16, 0]  # BV to [FD, CT, AS, BV]
    ]
    
    # Meeting indices: 0=Nancy, 1=Mary, 2=Jessica
    names = ["Nancy", "Mary", "Jessica"]
    durations = [90, 75, 45]  # in minutes
    min_starts = [30, 0, 135]  # earliest start times (minutes from 9:00 AM)
    max_ends = [270, 720, 285]  # latest end times (minutes from 9:00 AM)
    meeting_locs = [1, 2, 3]  # CT for Nancy, AS for Mary, BV for Jessica
    
    s = Solver()
    
    # Define meeting order variables
    first = Int('first')
    second = Int('second')
    third = Int('third')
    
    # Define start time variables
    s0 = Int('s0')  # first meeting start
    s1 = Int('s1')  # second meeting start
    s2 = Int('s2')  # third meeting start
    
    # Constraints for meeting indices
    s.add(Distinct(first, second, third))
    s.add(first >= 0, first <= 2)
    s.add(second >= 0, second <= 2)
    s.add(third >= 0, third <= 2)
    
    # Map meeting indices to locations
    loc0 = If(first == 0, meeting_locs[0], 
             If(first == 1, meeting_locs[1], meeting_locs[2]))
    loc1 = If(second == 0, meeting_locs[0],
             If(second == 1, meeting_locs[1], meeting_locs[2]))
    loc2 = If(third == 0, meeting_locs[0],
             If(third == 1, meeting_locs[1], meeting_locs[2]))
    
    # First meeting constraints (from FD to first location)
    s.add(s0 >= travel_matrix[0][loc0])  # travel from FD to first location
    s.add(s0 >= min_starts[first])       # within friend's availability
    s.add(s0 + durations[first] <= max_ends[first])
    
    # Second meeting constraints
    travel_time1 = travel_matrix[loc0][loc1]  # travel between locations
    s.add(s1 >= s0 + durations[first] + travel_time1)
    s.add(s1 >= min_starts[second])
    s.add(s1 + durations[second] <= max_ends[second])
    
    # Third meeting constraints
    travel_time2 = travel_matrix[loc1][loc2]  # travel between locations
    s.add(s2 >= s1 + durations[second] + travel_time2)
    s.add(s2 >= min_starts[third])
    s.add(s2 + durations[third] <= max_ends[third])
    
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