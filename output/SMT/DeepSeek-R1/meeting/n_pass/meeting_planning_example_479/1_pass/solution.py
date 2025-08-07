from z3 import *
import json

def main():
    # Data
    friends = [
        {"name": "Mary", "loc": 1, "start_avail": 525, "end_avail": 705, "min_dur": 45},
        {"name": "Kevin", "loc": 2, "start_avail": 615, "end_avail": 975, "min_dur": 90},
        {"name": "Deborah", "loc": 3, "start_avail": 900, "end_avail": 1155, "min_dur": 120},
        {"name": "Stephanie", "loc": 4, "start_avail": 600, "end_avail": 1035, "min_dur": 120},
        {"name": "Emily", "loc": 5, "start_avail": 690, "end_avail": 1305, "min_dur": 105}
    ]
    
    # Travel times: 6x6 matrix [Embarcadero, Golden Gate, Haight, Bayview, Presidio, Financial]
    T = [
        [0, 25, 21, 21, 20, 5],
        [25, 0, 7, 23, 11, 26],
        [20, 7, 0, 18, 15, 21],
        [19, 22, 19, 0, 31, 19],
        [20, 12, 15, 31, 0, 23],
        [4, 23, 19, 19, 22, 0]
    ]
    
    # Create solver
    opt = Optimize()
    
    # M[i]: whether we meet friend i
    M = [Bool(f"M_{i}") for i in range(5)]
    # t[i]: start time (in minutes) for meeting with friend i
    t = [Int(f"t_{i}") for i in range(5)]
    
    # x[i][j]: edge from node i to node j (j: 1 to 6; 1-5 are meetings, 6 is end)
    # x is a 6x6 matrix: rows i in [0,5] (nodes), columns j in [1,6] (stored as 0-5 indices: j=1->0, j=6->5)
    x = [[Bool(f"x_{i}_{j}") for j in range(6)] for i in range(6)]
    
    # (1) Start node (Embarcadero, node0) has one outgoing edge
    opt.add(Sum([x[0][j] for j in range(6)]) == 1)
    
    # (2) For meeting nodes 1 to 5 (node number n, friend index = n-1)
    for n in range(1, 6):  # n is node number
        friend_idx = n - 1
        # Incoming edges to node n: from any node i to node n -> x[i][n-1] (since j=n is at index n-1 in x[i])
        incoming = Sum([x[i][n-1] for i in range(6)])
        # Outgoing edges from node n: from node n to any j in [1,6] -> x[n][j] for j in 0..5 (representing j=1..6)
        outgoing = Sum([x[n][j] for j in range(6)])
        opt.add(incoming == If(M[friend_idx], 1, 0))
        opt.add(outgoing == If(M[friend_idx], 1, 0))
    
    # (3) End node (node6) has one incoming edge: j=6 is represented by index 5 in the edge list
    incoming_end = Sum([x[i][5] for i in range(6)])
    opt.add(incoming_end == 1)
    
    # (4) Time constraints for each friend if met
    for idx in range(5):
        opt.add(If(M[idx],
                   And(t[idx] >= friends[idx]["start_avail"], 
                       t[idx] + friends[idx]["min_dur"] <= friends[idx]["end_avail"]),
                   True))
    
    # (5) Edge time constraints for edges to meeting nodes (j in 1..5)
    for i in range(6):      # from node i
        for j in range(1,6): # to node j (meeting node, friend index j-1)
            j_index = j - 1  # index in the edge list for j
            if i == 0:
                # From start (node0) to meeting node j
                opt.add(If(x[0][j_index],
                           t[j-1] >= 540 + T[0][j],  # 540 is 9:00AM in minutes
                           True))
            else:
                # From meeting node i to meeting node j (i and j are node numbers, friend indices i-1 and j-1)
                opt.add(If(x[i][j_index],
                           t[j-1] >= t[i-1] + friends[i-1]["min_dur"] + T[i][j],
                           True))
    
    # Objective: maximize the number of meetings
    total_meetings = Sum([If(M_i, 1, 0) for M_i in M])
    opt.maximize(total_meetings)
    
    # Solve
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for idx in range(5):
            if is_true(model[M[idx]]):
                start_val = model[t[idx]].as_long()
                end_val = start_val + friends[idx]["min_dur"]
                # Format to HH:MM
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                schedule.append({
                    "action": "meet",
                    "person": friends[idx]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start time
        schedule.sort(key=lambda x: x["start_time"])
        result = {"itinerary": schedule}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()