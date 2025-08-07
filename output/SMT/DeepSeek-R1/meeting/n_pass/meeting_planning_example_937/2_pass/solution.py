from z3 import *
import json

def main():
    # Define the meetings (index 0 is the start at Russian Hill)
    meetings = [
        "Russian Hill",         # 0
        "Sunset District",      # 1: David
        "Union Square",         # 2: Kenneth
        "Nob Hill",             # 3: Patricia
        "Marina District",      # 4: Mary
        "Richmond District",    # 5: Charles
        "Financial District",   # 6: Joshua
        "Embarcadero",          # 7: Ronald
        "The Castro",            # 8: George
        "Alamo Square",         # 9: Kimberly
        "Presidio"              # 10: William
    ]
    n_meetings = len(meetings)
    
    # Friend names by meeting index (for indices 1 to 10)
    friend_names = {
        1: "David",
        2: "Kenneth",
        3: "Patricia",
        4: "Mary",
        5: "Charles",
        6: "Joshua",
        7: "Ronald",
        8: "George",
        9: "Kimberly",
        10: "William"
    }
    
    # Travel times data
    travel_data = [
        ("Russian Hill", "Sunset District", 23),
        ("Russian Hill", "Union Square", 10),
        ("Russian Hill", "Nob Hill", 5),
        ("Russian Hill", "Marina District", 7),
        ("Russian Hill", "Richmond District", 14),
        ("Russian Hill", "Financial District", 11),
        ("Russian Hill", "Embarcadero", 8),
        ("Russian Hill", "The Castro", 21),
        ("Russian Hill", "Alamo Square", 15),
        ("Russian Hill", "Presidio", 14),
        ("Sunset District", "Russian Hill", 24),
        ("Sunset District", "Union Square", 30),
        ("Sunset District", "Nob Hill", 27),
        ("Sunset District", "Marina District", 21),
        ("Sunset District", "Richmond District", 12),
        ("Sunset District", "Financial District", 30),
        ("Sunset District", "Embarcadero", 30),
        ("Sunset District", "The Castro", 17),
        ("Sunset District", "Alamo Square", 17),
        ("Sunset District", "Presidio", 16),
        ("Union Square", "Russian Hill", 13),
        ("Union Square", "Sunset District", 27),
        ("Union Square", "Nob Hill", 9),
        ("Union Square", "Marina District", 18),
        ("Union Square", "Richmond District", 20),
        ("Union Square", "Financial District", 9),
        ("Union Square", "Embarcadero", 11),
        ("Union Square", "The Castro", 17),
        ("Union Square", "Alamo Square", 15),
        ("Union Square", "Presidio", 24),
        ("Nob Hill", "Russian Hill", 5),
        ("Nob Hill", "Sunset District", 24),
        ("Nob Hill", "Union Square", 7),
        ("Nob Hill", "Marina District", 11),
        ("Nob Hill", "Richmond District", 14),
        ("Nob Hill", "Financial District", 9),
        ("Nob Hill", "Embarcadero", 9),
        ("Nob Hill", "The Castro", 17),
        ("Nob Hill", "Alamo Square", 11),
        ("Nob Hill", "Presidio", 17),
        ("Marina District", "Russian Hill", 8),
        ("Marina District", "Sunset District", 19),
        ("Marina District", "Union Square", 16),
        ("Marina District", "Nob Hill", 12),
        ("Marina District", "Richmond District", 11),
        ("Marina District", "Financial District", 17),
        ("Marina District", "Embarcadero", 14),
        ("Marina District", "The Castro", 22),
        ("Marina District", "Alamo Square", 15),
        ("Marina District", "Presidio", 10),
        ("Richmond District", "Russian Hill", 13),
        ("Richmond District", "Sunset District", 11),
        ("Richmond District", "Union Square", 21),
        ("Richmond District", "Nob Hill", 17),
        ("Richmond District", "Marina District", 9),
        ("Richmond District", "Financial District", 22),
        ("Richmond District", "Embarcadero", 19),
        ("Richmond District", "The Castro", 16),
        ("Richmond District", "Alamo Square", 13),
        ("Richmond District", "Presidio", 7),
        ("Financial District", "Russian Hill", 11),
        ("Financial District", "Sunset District", 30),
        ("Financial District", "Union Square", 9),
        ("Financial District", "Nob Hill", 8),
        ("Financial District", "Marina District", 15),
        ("Financial District", "Richmond District", 21),
        ("Financial District", "Embarcadero", 4),
        ("Financial District", "The Castro", 20),
        ("Financial District", "Alamo Square", 17),
        ("Financial District", "Presidio", 22),
        ("Embarcadero", "Russian Hill", 8),
        ("Embarcadero", "Sunset District", 30),
        ("Embarcadero", "Union Square", 10),
        ("Embarcadero", "Nob Hill", 10),
        ("Embarcadero", "Marina District", 12),
        ("Embarcadero", "Richmond District", 21),
        ("Embarcadero", "Financial District", 5),
        ("Embarcadero", "The Castro", 25),
        ("Embarcadero", "Alamo Square", 19),
        ("Embarcadero", "Presidio", 20),
        ("The Castro", "Russian Hill", 18),
        ("The Castro", "Sunset District", 17),
        ("The Castro", "Union Square", 19),
        ("The Castro", "Nob Hill", 16),
        ("The Castro", "Marina District", 21),
        ("The Castro", "Richmond District", 16),
        ("The Castro", "Financial District", 21),
        ("The Castro", "Embarcadero", 22),
        ("The Castro", "Alamo Square", 8),
        ("The Castro", "Presidio", 20),
        ("Alamo Square", "Russian Hill", 13),
        ("Alamo Square", "Sunset District", 16),
        ("Alamo Square", "Union Square", 14),
        ("Alamo Square", "Nob Hill", 11),
        ("Alamo Square", "Marina District", 15),
        ("Alamo Square", "Richmond District", 11),
        ("Alamo Square", "Financial District", 17),
        ("Alamo Square", "Embarcadero", 16),
        ("Alamo Square", "The Castro", 8),
        ("Alamo Square", "Presidio", 17),
        ("Presidio", "Russian Hill", 14),
        ("Presidio", "Sunset District", 15),
        ("Presidio", "Union Square", 22),
        ("Presidio", "Nob Hill", 18),
        ("Presidio", "Marina District", 11),
        ("Presidio", "Richmond District", 7),
        ("Presidio", "Financial District", 23),
        ("Presidio", "Embarcadero", 20),
        ("Presidio", "The Castro", 21),
        ("Presidio", "Alamo Square", 19)
    ]
    
    # Build a dictionary for travel times
    travel_dict = {}
    for (src, dst, t) in travel_data:
        travel_dict[(src, dst)] = t
        
    # Build travel_matrix: travel_matrix[i][j] = travel time from location of meeting i to meeting j
    travel_matrix = [[0] * n_meetings for _ in range(n_meetings)]
    for i in range(n_meetings):
        for j in range(n_meetings):
            if i == j:
                travel_matrix[i][j] = 0
            else:
                src_name = meetings[i]
                dst_name = meetings[j]
                travel_matrix[i][j] = travel_dict.get((src_name, dst_name), 1000000)  # large number if not found (should not happen)
    
    # Availability and duration for meetings (in minutes from 9:00 AM)
    # Index 0: dummy meeting at Russian Hill (start)
    avail_start = [0]   # for meeting0
    avail_end = [0]     # for meeting0
    min_dur = [0]       # for meeting0
    
    # Meeting 1: David
    avail_start.append(15)  # 9:15 AM
    avail_end.append(780)   # 10:00 PM (22:00) -> 13*60=780
    min_dur.append(15)
    
    # Meeting 2: Kenneth
    avail_start.append(735)  # 9:15 PM (21:15) -> 12*60+15 = 735? 9:00 AM to 9:00 PM is 12 hours (720 minutes), then 15 min -> 735
    avail_end.append(765)    # 9:45 PM (21:45) -> 720+45=765
    min_dur.append(15)
    
    # Meeting 3: Patricia
    avail_start.append(360)  # 3:00 PM (15:00) -> 6*60=360
    avail_end.append(615)    # 7:15 PM (19:15) -> 10*60+15=615
    min_dur.append(120)
    
    # Meeting 4: Mary
    avail_start.append(345)  # 2:45 PM (14:45) -> 5*60+45=345
    avail_end.append(465)    # 4:45 PM (16:45) -> 7*60+45=465
    min_dur.append(45)
    
    # Meeting 5: Charles
    avail_start.append(495)  # 5:15 PM (17:15) -> 8*60+15=495
    avail_end.append(720)    # 9:00 PM (21:00) -> 12*60=720
    min_dur.append(15)
    
    # Meeting 6: Joshua
    avail_start.append(330)  # 2:30 PM (14:30) -> 5*60+30=330
    avail_end.append(495)    # 5:15 PM (17:15) -> 8*60+15=495
    min_dur.append(90)
    
    # Meeting 7: Ronald
    avail_start.append(555)  # 6:15 PM (18:15) -> 9*60+15=555
    avail_end.append(705)    # 8:45 PM (20:45) -> 11*60+45=705
    min_dur.append(30)
    
    # Meeting 8: George
    avail_start.append(315)  # 2:15 PM (14:15) -> 5*60+15=315
    avail_end.append(600)    # 7:00 PM (19:00) -> 10*60=600
    min_dur.append(105)
    
    # Meeting 9: Kimberly
    avail_start.append(0)    # 9:00 AM
    avail_end.append(330)    # 2:30 PM (14:30) -> 5*60+30=330
    min_dur.append(105)
    
    # Meeting 10: William
    avail_start.append(0)    # 9:00 AM
    avail_end.append(225)    # 12:45 PM (12:45) -> 3*60+45=225
    min_dur.append(60)
    
    # Create Z3 solver
    s = Optimize()  # Use Optimize instead of Solver for maximization
    
    # met_list[i] indicates if meeting i is met (for i=0, it's always True; for i=1..10, it's a variable)
    met_list = [True]  # for meeting0
    for i in range(1, n_meetings):
        met_list.append(Bool(f"met_{i}"))
    
    # start and end times for each meeting (in minutes from 9:00 AM)
    start_times = [Int(f"start_{i}") for i in range(n_meetings)]
    end_times = [Int(f"end_{i}") for i in range(n_meetings)]
    
    # order[i]: the position of meeting i in the sequence (if met)
    orders = [Int(f"order_{i}") for i in range(n_meetings)]
    
    # Constraints for meeting0 (start at Russian Hill)
    s.add(start_times[0] == 0)
    s.add(end_times[0] == 0)
    s.add(orders[0] == 0)
    
    # Constraints for meetings 1 to 10
    for i in range(1, n_meetings):
        # If meeting i is met, then it must be within availability and have at least min_dur
        s.add(Implies(met_list[i],
                     And(start_times[i] >= avail_start[i],
                         end_times[i] == start_times[i] + min_dur[i],
                         end_times[i] <= avail_end[i])))
    
    # Constraints for orders
    # For meetings that are met, the order must be between 0 and 10 (for meeting0, it's fixed to 0)
    # For meetings 1 to 10, if met, order must be between 1 and 10
    for i in range(1, n_meetings):
        s.add(Implies(met_list[i], And(orders[i] >= 1, orders[i] <= 10)))
    
    # Distinct orders for meetings that are met
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            s.add(Implies(And(met_list[i], met_list[j]), orders[i] != orders[j]))
    
    # Travel constraints for every pair (i,j) with i != j and both met
    for i in range(n_meetings):
        for j in range(n_meetings):
            if i == j:
                continue
            # If both meetings are met, then either i is before j or j is before i
            cond = And(met_list[i], met_list[j])
            # If i is before j, then end_i + travel(i->j) <= start_j
            before_ij = And(orders[i] < orders[j], end_times[i] + travel_matrix[i][j] <= start_times[j])
            # If j is before i, then end_j + travel(j->i) <= start_i
            before_ji = And(orders[j] < orders[i], end_times[j] + travel_matrix[j][i] <= start_times[i])
            s.add(Implies(cond, Or(before_ij, before_ji)))
    
    # Maximize the number of friends met (i.e., meetings 1 to 10)
    objective = Sum([If(met_list[i], 1, 0) for i in range(1, n_meetings)])
    s.maximize(objective)
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        # Extract the meetings that are met
        itinerary = []
        for i in range(1, n_meetings):
            if is_true(model.eval(met_list[i])):
                start_val = model.eval(start_times[i]).as_long()
                end_val = model.eval(end_times[i]).as_long()
                # Convert minutes to time string (from 9:00 AM)
                total_minutes_start = start_val
                hours_start = total_minutes_start // 60
                minutes_start = total_minutes_start % 60
                # Since we start at 9:00 AM, actual hour = 9 + hours_start
                actual_hour_start = 9 + hours_start
                actual_minute_start = minutes_start
                start_time_str = f"{actual_hour_start:02d}:{actual_minute_start:02d}"
                
                total_minutes_end = end_val
                hours_end = total_minutes_end // 60
                minutes_end = total_minutes_end % 60
                actual_hour_end = 9 + hours_end
                actual_minute_end = minutes_end
                end_time_str = f"{actual_hour_end:02d}:{actual_minute_end:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "person": friend_names[i],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("SOLUTION:")
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()