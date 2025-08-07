from z3 import *

def main():
    # Initialize the solver with optimization
    s = Optimize()

    # Define meetings: [Richard, Stephanie, Brian, Sandra, Jason]
    meet = [Bool(f"meet_{i}") for i in range(5)]
    start = [Int(f"start_{i}") for i in range(5)]
    
    # Availability and duration for each meeting (in minutes since midnight)
    avail_start = [435, 495, 735, 780, 510]  # Richard, Stephanie, Brian, Sandra, Jason
    avail_end = [615, 825, 960, 1170, 1065]
    durations = [75, 90, 120, 15, 60]
    names = ["Richard", "Stephanie", "Brian", "Sandra", "Jason"]
    
    # Travel time matrix (6x6: locations 0 to 5)
    # Locations: 0=Haight-Ashbury, 1=Pacific Heights, 2=Mission District, 3=Russian Hill, 4=Bayview, 5=Fisherman's Wharf
    T = [
        [0, 12, 11, 17, 18, 23],
        [11, 0, 15, 7, 22, 13],
        [12, 16, 0, 15, 15, 22],
        [17, 7, 16, 0, 23, 7],
        [19, 23, 13, 23, 0, 25],
        [22, 12, 22, 7, 26, 0]
    ]
    
    # Map meeting index to location index (0-based meeting index to 1-based location index)
    meeting_to_loc = [1, 2, 3, 4, 5]  # Richard->loc1, Stephanie->loc2, etc.
    
    # Constraints for each meeting
    for i in range(5):
        s.add(Implies(meet[i], start[i] >= avail_start[i]))
        s.add(Implies(meet[i], start[i] + durations[i] <= avail_end[i]))
    
    # Start at Haight-Ashbury (loc0) at 540 minutes (9:00 AM)
    start_loc_time = 540
    
    # Constraints from start location to each meeting
    for i in range(5):
        loc_i = meeting_to_loc[i]
        s.add(Implies(meet[i], start[i] >= start_loc_time + T[0][loc_i]))
    
    # Constraints between every pair of meetings
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            loc_i = meeting_to_loc[i]
            loc_j = meeting_to_loc[j]
            travel_ij = T[loc_i][loc_j]
            travel_ji = T[loc_j][loc_i]
            end_i = start[i] + durations[i]
            end_j = start[j] + durations[j]
            disj = Or(
                end_i + travel_ij <= start[j],
                end_j + travel_ji <= start[i]
            )
            s.add(Implies(And(meet[i], meet[j]), disj))
    
    # Objective: maximize the number of meetings
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(5)])
    s.maximize(total_meetings)
    
    # Solve and extract the itinerary
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for i in range(5):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(start[i]).as_long()
                end_val = start_val + durations[i]
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                scheduled_meetings.append((start_val, {
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_str,
                    "end_time": end_str
                }))
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = [entry[1] for entry in scheduled_meetings]
        result = {"itinerary": itinerary}
        print(f"SOLUTION: {result}")
    else:
        print("SOLUTION: {\"itinerary\": []}")

if __name__ == "__main__":
    main()