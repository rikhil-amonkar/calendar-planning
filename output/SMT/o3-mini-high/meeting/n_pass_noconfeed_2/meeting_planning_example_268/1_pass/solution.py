import json
from z3 import *

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Create an Optimize object.
    opt = Optimize()

    # Define friend information.
    # Times are in minutes from midnight.
    # Golden Gate Park arrival time: 9:00 AM = 540.
    # Timothy: available 12:00 (720) to 16:15 (975), min meeting 105 minutes, location "Alamo Square"
    # Mark: available 18:45 (1125) to 21:00 (1260), min meeting 60 minutes, location "Presidio"
    # Joseph: available 16:45 (1005) to 21:30 (1290), min meeting 60 minutes, location "Russian Hill"
    friends = [
        {"name": "Timothy", "location": "Alamo Square", "avail_start": 720, "avail_end": 975, "min_dur": 105},
        {"name": "Mark",    "location": "Presidio",      "avail_start": 1125, "avail_end": 1260, "min_dur": 60},
        {"name": "Joseph",  "location": "Russian Hill",  "avail_start": 1005, "avail_end": 1290, "min_dur": 60}
    ]
    
    # Travel time from Golden Gate Park to each friend's location.
    # Index 0: Alamo Square, 1: Presidio, 2: Russian Hill.
    ggp_to = [10, 11, 19]
    
    # Matrix of travel times (in minutes) between the friends' locations.
    # Order in friends list: 0 -> Alamo Square, 1 -> Presidio, 2 -> Russian Hill.
    # For example, travel[0][1] is travel time from Alamo Square to Presidio.
    travel = [
        [0, 18, 13],  # From Alamo Square to Presidio: 18, to Russian Hill: 13.
        [18, 0, 14],  # From Presidio to Alamo Square: 18, to Russian Hill: 14.
        [15, 14, 0]   # From Russian Hill to Alamo Square: 15, to Presidio: 14.
    ]
    
    # Decision variables for the ordering of meetings.
    # We embed the order as three integer variables which represent indices in {0,1,2}.
    pos1 = Int('pos1')
    pos2 = Int('pos2')
    pos3 = Int('pos3')
    opt.add(And(pos1 >= 0, pos1 < 3))
    opt.add(And(pos2 >= 0, pos2 < 3))
    opt.add(And(pos3 >= 0, pos3 < 3))
    opt.add(Distinct(pos1, pos2, pos3))
    
    # Meeting start and end time variables for each friend (in minutes from midnight).
    S = [Int(f"S_{i}") for i in range(3)]
    E = [Int(f"E_{i}") for i in range(3)]
    
    # Add constraints for each friend's meeting availability and minimum duration.
    for i, f in enumerate(friends):
        # Meeting must start no earlier than the friend's available start.
        opt.add(S[i] >= f["avail_start"])
        # Meeting must end no later than the friend's available end.
        opt.add(E[i] <= f["avail_end"])
        # Meeting duration must be at least the minimum required.
        opt.add(E[i] - S[i] >= f["min_dur"])
    
    # Constraint for the first meeting: must account for travel from Golden Gate Park.
    # We require: if friend i is scheduled first (pos1 == i) then S[i] >= arrival time + travel time.
    for i in range(3):
        opt.add(Implies(pos1 == i, S[i] >= 540 + ggp_to[i]))
    
    # Constraint for ordering between the first and second meeting.
    # If friend i is first and friend j is second, then meeting j must start after finishing i plus travel time.
    for i in range(3):
        for j in range(3):
            if i != j:
                opt.add(Implies(And(pos1 == i, pos2 == j),
                                  S[j] >= E[i] + travel[i][j]))
                
    # Constraint for ordering between the second and third meeting.
    for i in range(3):
        for j in range(3):
            if i != j:
                opt.add(Implies(And(pos2 == i, pos3 == j),
                                  S[j] >= E[i] + travel[i][j]))
    
    # Define finish_time as the end time of the meeting that is scheduled last (at pos3).
    finish_time = Int('finish_time')
    finish_time_expr = If(pos3 == 0, E[0], If(pos3 == 1, E[1], E[2]))
    opt.add(finish_time == finish_time_expr)
    
    # Set objective: minimize the finish time of the itinerary.
    opt.minimize(finish_time)
    
    # Check for satisfiability and get the optimal model.
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        # Retrieve the itinerary order: pos1, pos2, pos3.
        order_vars = [pos1, pos2, pos3]
        for pos_var in order_vars:
            friend_index = m.eval(pos_var).as_long()
            start_time = m.eval(S[friend_index]).as_long()
            end_time = m.eval(E[friend_index]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[friend_index]["location"],
                "person": friends[friend_index]["name"],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no valid schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()