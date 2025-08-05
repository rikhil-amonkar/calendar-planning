from z3 import *
import json

def main():
    # Names of friends
    names = ['Robert', 'Michelle', 'George', 'William']
    
    # Durations for each friend in minutes
    dur = [30, 15, 30, 105]
    
    # Availability start times in minutes from 9:00 AM (base time)
    avail_start = [0, -45, 90, 570]  # Robert, Michelle, George, William
    
    # Availability end times in minutes from 9:00 AM
    avail_end = [285, 300, 585, 705]  # 1:45 PM, 2:00 PM, 6:45 PM, 8:45 PM
    
    # Travel times from Sunset District to each friend's location
    travel_start = [29, 30, 16, 24]  # to Robert, Michelle, George, William
    
    # Travel times between friends: [from][to] = time in minutes
    travel_between = [
        [0, 12, 17, 7],   # from Robert to [Robert, Michelle, George, William]
        [8, 0, 19, 7],    # from Michelle
        [19, 21, 0, 14],  # from George
        [7, 9, 14, 0]     # from William
    ]
    
    # Define Z3 solver
    s = Solver()
    
    # Define Z3 functions for durations, availability, and travel times
    dur_z3 = Function('dur', IntSort(), IntSort())
    avail_start_z3 = Function('avail_start', IntSort(), IntSort())
    avail_end_z3 = Function('avail_end', IntSort(), IntSort())
    travel_start_z3 = Function('travel_start', IntSort(), IntSort())
    travel_between_z3 = Function('travel_between', IntSort(), IntSort(), IntSort())
    
    # Initialize function values
    for i in range(4):
        s.add(dur_z3(i) == dur[i])
        s.add(avail_start_z3(i) == avail_start[i])
        s.add(avail_end_z3(i) == avail_end[i])
        s.add(travel_start_z3(i) == travel_start[i])
        for j in range(4):
            s.add(travel_between_z3(i, j) == travel_between[i][j])
    
    # Meeting order variables (each can be 0, 1, 2, 3)
    m0, m1, m2, m3 = Ints('m0 m1 m2 m3')
    # Start time variables for each meeting
    S0, S1, S2, S3 = Ints('S0 S1 S2 S3')
    
    # Constraints: each meeting index is between 0 and 3 and all are distinct
    s.add(Distinct(m0, m1, m2, m3))
    for m_var in [m0, m1, m2, m3]:
        s.add(m_var >= 0, m_var <= 3)
    
    # Constraints for the first meeting (from Sunset to m0)
    s.add(S0 >= travel_start_z3(m0))
    s.add(S0 >= avail_start_z3(m0))
    s.add(S0 + dur_z3(m0) <= avail_end_z3(m0))
    
    # Constraints for the second meeting (from m0 to m1)
    s.add(S1 >= S0 + dur_z3(m0) + travel_between_z3(m0, m1))
    s.add(S1 >= avail_start_z3(m1))
    s.add(S1 + dur_z3(m1) <= avail_end_z3(m1))
    
    # Constraints for the third meeting (from m1 to m2)
    s.add(S2 >= S1 + dur_z3(m1) + travel_between_z3(m1, m2))
    s.add(S2 >= avail_start_z3(m2))
    s.add(S2 + dur_z3(m2) <= avail_end_z3(m2))
    
    # Constraints for the fourth meeting (from m2 to m3)
    s.add(S3 >= S2 + dur_z3(m2) + travel_between_z3(m2, m3))
    s.add(S3 >= avail_start_z3(m3))
    s.add(S3 + dur_z3(m3) <= avail_end_z3(m3))
    
    # Check for satisfiability
    if s.check() == sat:
        model = s.model()
        m0_val = model[m0].as_long()
        m1_val = model[m1].as_long()
        m2_val = model[m2].as_long()
        m3_val = model[m3].as_long()
        S0_val = model[S0].as_long()
        S1_val = model[S1].as_long()
        S2_val = model[S2].as_long()
        S3_val = model[S3].as_long()
        
        # Function to convert minutes from 9:00 AM to HH:MM format
        def format_time(minutes):
            total_minutes = minutes
            hours = 9 + total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        # Create meeting entries in chronological order
        itinerary = []
        
        # Meeting 0
        start0 = S0_val
        end0 = S0_val + dur[m0_val]
        itinerary.append({
            "action": "meet",
            "person": names[m0_val],
            "start_time": format_time(start0),
            "end_time": format_time(end0)
        })
        
        # Meeting 1
        start1 = S1_val
        end1 = S1_val + dur[m1_val]
        itinerary.append({
            "action": "meet",
            "person": names[m1_val],
            "start_time": format_time(start1),
            "end_time": format_time(end1)
        })
        
        # Meeting 2
        start2 = S2_val
        end2 = S2_val + dur[m2_val]
        itinerary.append({
            "action": "meet",
            "person": names[m2_val],
            "start_time": format_time(start2),
            "end_time": format_time(end2)
        })
        
        # Meeting 3
        start3 = S3_val
        end3 = S3_val + dur[m3_val]
        itinerary.append({
            "action": "meet",
            "person": names[m3_val],
            "start_time": format_time(start3),
            "end_time": format_time(end3)
        })
        
        # Output the itinerary as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no solution found, output empty itinerary
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()