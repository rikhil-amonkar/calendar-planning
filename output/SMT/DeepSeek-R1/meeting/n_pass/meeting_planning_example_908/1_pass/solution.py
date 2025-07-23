from z3 import *
import datetime

def main():
    # Define the travel_time matrix (11x11): rows 0..10, columns 0..10
    # Index: 0: Financial District, 1: Fisherman's Wharf, 2: Presidio, 3: Bayview, 4: Haight-Ashbury, 
    #         5: Russian Hill, 6: The Castro, 7: Marina District, 8: Richmond District, 9: Union Square, 10: Sunset District
    travel_time = [
        [0, 10, 22, 19, 19, 11, 20, 15, 21, 9, 30],
        [11, 0, 17, 26, 22, 7, 27, 9, 18, 13, 27],
        [23, 19, 0, 31, 15, 14, 21, 11, 7, 22, 15],
        [19, 25, 32, 0, 19, 23, 19, 27, 25, 18, 23],
        [21, 23, 15, 18, 0, 17, 6, 17, 10, 19, 15],
        [11, 7, 14, 23, 17, 0, 21, 7, 14, 10, 23],
        [21, 24, 20, 19, 6, 18, 0, 21, 16, 19, 17],
        [17, 10, 10, 27, 16, 8, 22, 0, 11, 16, 19],
        [22, 18, 7, 27, 10, 13, 16, 9, 0, 21, 11],
        [9, 15, 24, 15, 18, 13, 17, 18, 20, 0, 27],
        [30, 29, 16, 22, 15, 24, 17, 21, 12, 30, 0]
    ]
    
    # Define meeting details: index 0 for meeting 1 (Mark), 1 for meeting 2 (Stephanie), ... 9 for meeting 10 (Karen)
    window_start_minutes = [0, 195, 0, 390, 585, 15, 105, 45, 450, 450]  # from 9:00 AM in minutes
    window_end_minutes = [60, 360, 690, 570, 660, 255, 360, 135, 660, 780]  # from 9:00 AM in minutes
    min_durations = [30, 75, 15, 45, 60, 30, 90, 45, 120, 105]  # in minutes
    friend_names = {
        1: "Mark",
        2: "Stephanie",
        3: "Betty",
        4: "Lisa",
        5: "William",
        6: "Brian",
        7: "Joseph",
        8: "Ashley",
        9: "Patricia",
        10: "Karen"
    }
    
    n_nodes = 11  # nodes 0..10 (start and meetings)
    end_node = 11  # end node index
    n_meetings = 10  # meetings 1..10

    # Create solver
    s = Optimize()
    
    # Define next variables for nodes 0..10
    next_vars = [Int(f'next_{i}') for i in range(n_nodes)]
    
    # Define visited for meetings 1..10: visited[0] for meeting1, ... visited[9] for meeting10
    visited = [Bool(f'visited_{i}') for i in range(1, 11)]
    
    # Define start_time and end_time for meetings 1..10: start_time[i] for meeting i+1
    start_time = [Int(f'start_{i}') for i in range(1, 11)]
    end_time = [Int(f'end_{i}') for i in range(1, 11)]
    
    # Constraints for next_vars: each next[i] is in [1,11] and for i>=1, next[i] != i
    for i in range(n_nodes):
        s.add(And(next_vars[i] >= 1, next_vars[i] <= 11))
        if i >= 1:  # meetings 1..10 cannot point to themselves
            s.add(next_vars[i] != i+1)  # because meeting index is i+1 for node i (since node0 is start, node1 is meeting1, etc.)
    
    # Constraint: for each meeting j (1..10), visited[j-1] is true iff there exists i in [0,10] such that next_vars[i] == j
    for j in range(1, 11):
        # visited[j-1] == Or_{i=0..10} (next_vars[i] == j)
        s.add(visited[j-1] == Or([next_vars[i] == j for i in range(n_nodes)]))
        # At most one i has next_vars[i] == j
        s.add(Sum([If(next_vars[i] == j, 1, 0) for i in range(n_nodes)]) <= 1)
    
    # Time constraints for each meeting j (1..10)
    for j in range(1, 11):
        idx = j-1  # index in the lists for this meeting
        base = 0
        for i in range(n_nodes):  # i from 0 to 10
            # If next_vars[i] == j, then the time to get to j is (if i==0: 0 else end_time[i-1]) + travel_time[i][j-1]
            # Note: for meeting j, the district index is j-1? 
            # But in the travel_time matrix: from node i (which has district index i) to meeting j (which is at district index j-1) -> travel_time[i][j-1]
            # However, note: our travel_time matrix is 11x11 for districts 0..10, and meeting j is at district index j (since meeting1 is at district1, which is index1 in the matrix) -> so we use travel_time[i][j]
            # But our travel_time matrix: row i (district i) to column j (district j) -> for meeting j, we use travel_time[i][j] because meeting j is at district j (index j in the matrix, which is the same as the meeting number)
            # However, the meeting number j corresponds to district j? 
            # Yes: meeting1 (j=1) is at district1 (Fisherman's Wharf)
            # So travel_time from node i (district i) to meeting j (district j) is travel_time[i][j]
            # But note: the matrix is 11x11, and j is from 1 to 10, so travel_time[i][j] is defined.
            if i == 0:
                # from start (district0) to meeting j (district j)
                contrib = If(next_vars[i] == j, travel_time[i][j], 0)
            else:
                # from meeting i (district i) to meeting j (district j): 
                # note: meeting i is represented by node i, and its end_time is end_time[i-1] (because meetings 1..10 are at indices 0..9)
                contrib = If(next_vars[i] == j, end_time[i-1] + travel_time[i][j], 0)
            base += contrib
        
        # If visited, then start_time[j-1] >= base and >= window_start, and end_time = start_time + duration, and end_time <= window_end
        s.add(If(visited[idx],
                 And(
                     start_time[idx] >= base,
                     start_time[idx] >= window_start_minutes[idx],
                     end_time[idx] == start_time[idx] + min_durations[idx],
                     end_time[idx] <= window_end_minutes[idx]
                 ),
                 True  # if not visited, no constraints
        ))
    
    # Maximize the number of visited meetings
    total_visited = Sum([If(v, 1, 0) for v in visited])
    s.maximize(total_visited)
    
    # Solve
    if s.check() == sat:
        model = s.model()
        total_visited_val = model.eval(total_visited).as_long()
        print(f"Total meetings visited: {total_visited_val}")
        
        # Reconstruct the itinerary
        itinerary = []
        current = model.eval(next_vars[0]).as_long()  # next after start
        while current != end_node and current is not None:
            # current is the meeting node (1..10)
            meeting_index = current  # 1..10
            idx = meeting_index - 1  # index in lists
            if not model.eval(visited[idx]):
                break
            start_min = model.eval(start_time[idx]).as_long()
            end_min = model.eval(end_time[idx]).as_long()
            
            # Convert minutes to time strings
            start_time_str = (datetime.datetime(2023,1,1,9,0) + datetime.timedelta(minutes=start_min)).strftime("%H:%M")
            end_time_str = (datetime.datetime(2023,1,1,9,0) + datetime.timedelta(minutes=end_min)).strftime("%H:%M")
            
            itinerary.append({
                "action": "meet",
                "person": friend_names[meeting_index],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
            
            # Next node: from the current meeting node
            current = model.eval(next_vars[meeting_index]).as_long()  # next after this meeting (could be end_node or another meeting)
        
        # Output as JSON
        print("SOLUTION:")
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()